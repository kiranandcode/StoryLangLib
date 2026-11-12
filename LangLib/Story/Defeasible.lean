/-!
# Defeasible logic for character plausibility

Ground defeasible logic (Nute; Antoniou, Billington, Governatori & Maher 2001)
with a superiority relation read off each character's ranking of values
(Bench-Capon's value-based argumentation).

* strict rules `body → head` always hold;
* defeasible rules `body ⇒ head` hold unless beaten;
* defeaters `body ⇝ head` only block the opposite conclusion.

A defeasible rule may name the agent whose value it serves; between two rules of
the same agent the one serving the more preferred value wins. Strict rules beat
every non-strict rule.

`Theory.verdict` asks whether a literal (typically "X does action A") is
defeasibly provable (plausible), its negation is (implausible), or neither
(unexplained), and returns the rules involved, so the answer can be shown to an
author or sent back to an LLM as a "justification debt".

This is an evaluator only; a soundness proof against the inductive proof theory
is future work.
-/

namespace LangLib.Story

structure Atom where
  pred : String
  args : List String
  deriving Repr, DecidableEq, Hashable, Inhabited

def Atom.show (a : Atom) : String := s!"{a.pred}({", ".intercalate a.args})"

structure Lit where
  atom : Atom
  pos : Bool := true
  deriving Repr, DecidableEq, Hashable, Inhabited

def Lit.neg (l : Lit) : Lit := { l with pos := !l.pos }
def Lit.show (l : Lit) : String := (if l.pos then "" else "¬") ++ l.atom.show

def lit (pred : String) (args : List String) : Lit := ⟨⟨pred, args⟩, true⟩
def nlit (pred : String) (args : List String) : Lit := ⟨⟨pred, args⟩, false⟩

inductive RuleKind | strict | defeasible | defeater
  deriving Repr, DecidableEq, Inhabited

structure Rule where
  name : String
  kind : RuleKind
  body : List Lit
  head : Lit
  /-- whose value this rule serves, and which value -/
  agent : Option String := none
  value : Option String := none
  deriving Repr, Inhabited

/-- A character's values, most preferred first. -/
structure Persona where
  name : String
  values : List String
  deriving Repr, Inhabited

def Persona.prefers (p : Persona) (a b : String) : Bool :=
  match p.values.idxOf? a, p.values.idxOf? b with
  | some i, some j => i < j
  | some _, none => true
  | _, _ => false

structure Theory where
  facts : List Lit
  rules : List Rule
  personas : List Persona := []
  deriving Inhabited

def Theory.sup (T : Theory) (r s : Rule) : Bool :=
  (r.kind == .strict && s.kind != .strict) ||
  (r.kind != .strict && s.kind != .strict &&
   match r.agent, s.agent, r.value, s.value with
   | some a, some b, some v, some w =>
     a == b && ((T.personas.find? (·.name == a)).map (·.prefers v w)).getD false
   | _, _, _, _ => false)

/-- Every literal the theory talks about, and their negations. -/
def Theory.literals (T : Theory) : List Lit :=
  let ls := T.facts ++ T.rules.flatMap (fun r => r.head :: r.body)
  (ls ++ ls.map Lit.neg).eraseDups

/-- Definite (strict) consequences: forward chaining over facts and strict rules. -/
partial def Theory.definite (T : Theory) : List Lit :=
  let step (known : List Lit) : List Lit :=
    T.rules.foldl (fun acc r =>
      if r.kind == .strict && r.body.all acc.contains && !acc.contains r.head
      then acc ++ [r.head] else acc) known
  let rec go (known : List Lit) : List Lit :=
    let next := step known
    if next.length == known.length then known else go next
  go T.facts.eraseDups

inductive Status | yes | no | unknown
  deriving Repr, DecidableEq, Inhabited

structure Eval where
  definite : List Lit
  /-- +∂ and −∂ found by iterating to a fixpoint; anything left is −∂ -/
  plus : List Lit
  minus : List Lit

/-- Compute +∂ / −∂ for every literal of the theory. -/
partial def Theory.eval (T : Theory) : Eval :=
  let defs := T.definite
  let lits := T.literals
  let supporting (q : Lit) := T.rules.filter fun r => r.head == q && r.kind != .defeater
  let attacking (q : Lit) := T.rules.filter fun r => r.head == q.neg
  let rec go (plus minus : List Lit) : List Lit × List Lit :=
    let applicable (r : Rule) := r.body.all plus.contains
    let discarded (r : Rule) := r.body.any minus.contains
    let (p', m') := lits.foldl (fun (p, m) q =>
      if p.contains q || m.contains q then (p, m)
      else if defs.contains q then (p ++ [q], m)
      else
        let sup := supporting q
        let att := attacking q
        let provable :=
          sup.any applicable && !defs.contains q.neg &&
          att.all fun s => discarded s || sup.any fun t => applicable t && T.sup t s
        let refuted :=
          sup.all discarded || defs.contains q.neg ||
          att.any fun s => applicable s && sup.all fun t => discarded t || !T.sup t s
        if provable then (p ++ [q], m) else if refuted then (p, m ++ [q]) else (p, m))
      (plus, minus)
    if p'.length == plus.length && m'.length == minus.length then (plus, minus)
    else go p' m'
  let (plus, minus) := go [] []
  { definite := defs, plus, minus := minus ++ lits.filter fun q => !plus.contains q && !minus.contains q }

/-- Why a literal was or was not concluded. -/
inductive Verdict where
  /-- the opposite is strictly derivable -/
  | impossible (by_ : List Rule)
  /-- defeasibly provable: the winning rules, and the attacks each beat -/
  | plausible (winners : List Rule) (beaten : List Rule)
  /-- the negation is defeasibly provable; `repairs` are rules for the literal
  whose bodies, if established, could make it plausible -/
  | implausible (blockers : List Rule) (repairs : List (Rule × List Lit))
  /-- neither it nor its negation follows -/
  | unexplained (repairs : List (Rule × List Lit))
  deriving Inhabited

def Theory.verdict (T : Theory) (q : Lit) : Verdict :=
  let e := T.eval
  let applicable (r : Rule) := r.body.all e.plus.contains
  let repairs := (T.rules.filter fun r => r.head == q && r.kind != .defeater && !applicable r).map
    fun r => (r, r.body.filter fun b => !e.plus.contains b)
  if e.definite.contains q.neg then
    .impossible (T.rules.filter fun r => r.kind == .strict && r.head == q.neg && applicable r)
  else if e.plus.contains q then
    .plausible (T.rules.filter fun r => r.head == q && r.kind != .defeater && applicable r)
      (T.rules.filter fun r => r.head == q.neg && applicable r)
  else if e.plus.contains q.neg then
    .implausible (T.rules.filter fun r => r.head == q.neg && r.kind != .defeater && applicable r)
      repairs
  else .unexplained repairs

def Verdict.tag : Verdict → String
  | .impossible .. => "impossible" | .plausible .. => "plausible"
  | .implausible .. => "implausible" | .unexplained .. => "unexplained"

private def ruleShow (r : Rule) : String :=
  let v := match r.value with | some v => s!" [{v}]" | none => ""
  s!"{r.name}{v}"

private def repairShow (rs : List (Rule × List Lit)) : String :=
  "; ".intercalate (rs.map fun (r, missing) =>
    s!"{ruleShow r} needs {", ".intercalate (missing.map Lit.show)}")

/-- A message for an author or an LLM. -/
def Verdict.explain (q : Lit) : Verdict → String
  | .impossible rs => s!"{q.show} is impossible: {", ".intercalate (rs.map ruleShow)}"
  | .plausible ws bs =>
    let beat := if bs.isEmpty then "" else s!", overriding {", ".intercalate (bs.map ruleShow)}"
    s!"{q.show} is plausible by {", ".intercalate (ws.map ruleShow)}{beat}"
  | .implausible bs rs =>
    s!"{q.show} is out of character ({", ".intercalate (bs.map ruleShow)}). " ++
    s!"Revise it, or establish setup first: {repairShow rs}"
  | .unexplained rs =>
    s!"{q.show} is unmotivated. Possible motivations: {repairShow rs}"

end LangLib.Story
