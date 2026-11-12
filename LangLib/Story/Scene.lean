import LangLib.Story.DL

/-!
# Scenes

A scene is a state (where everyone is, who holds what, who knows what, who is
threatening whom) and a list of events. A story is `Valid` when every event

1. meets its hard preconditions (`pre`): you can only take an object lying
   where you stand, only talk to someone in the same place, and only tell what
   you know; and
2. is in character (`InCharacter`): for a shout, the defeasible theory of the
   agent's persona and situation must not prove that they would stay quiet.

Knowledge comes only from observation: everyone in the place where an event
happens learns its visible effect, and `tell` passes a fact on.

`validB` decides `Valid` (`validB_sound`), with the plausibility part checked
through a defeasible-logic certificate, so a scene's validity is proved by
`decide`. `explain` gives the author-facing reasons.
-/

namespace LangLib.Scene
open LangLib.DL

inductive Trait | timid | brash
  deriving DecidableEq, Repr

inductive Value | safety | loyalty | pride
  deriving DecidableEq, Repr

variable {C P O : Type} [DecidableEq C] [DecidableEq P] [DecidableEq O]

/-- What a character can know. -/
inductive Fact (C P O : Type) where
  | at_ (c : C) (p : P)
  | objAt (o : O) (p : P)
  | holds (c : C) (o : O)
  deriving DecidableEq, Repr

inductive Event (C P O : Type) where
  | move (c : C) (p : P)
  | take (c : C) (o : O)
  /-- put down a held object where you stand -/
  | hide (c : C) (o : O)
  /-- `c` lays hands on `v` -/
  | grab (c v : C)
  | shout (c d : C)
  | tell (c d : C) (f : Fact C P O)
  | gag (c v : C)
  | drink (c : C)
  deriving DecidableEq, Repr

structure Persona (C : Type) where
  traits : List Trait
  /-- most preferred first -/
  values : List Value
  allies : List C

structure State (C P O : Type) where
  persona : C → Persona C
  loc : C → P
  holder : O → Option C
  objLoc : O → P
  gagged : C → Bool := fun _ => false
  drunk : C → Bool := fun _ => false
  threats : List (C × C) := []
  knows : C → List (Fact C P O) := fun _ => []

/-! ## Hard constraints and effects -/

def pre (s : State C P O) : Event C P O → Bool
  | .move _ _ => true
  | .take c o => s.holder o == none && s.objLoc o == s.loc c
  | .hide c o => s.holder o == some c
  | .grab c v => c != v && s.loc c == s.loc v
  | .shout c d => s.loc c == s.loc d && !s.gagged c
  | .tell c d f => s.loc c == s.loc d && !s.gagged c && (s.knows c).contains f
  | .gag c v => s.loc c == s.loc v
  | .drink _ => true

/-- Everyone at `p` learns `f`. -/
def State.witness (s : State C P O) (p : P) (f : Fact C P O) : State C P O :=
  { s with knows := fun x => if s.loc x == p then f :: s.knows x else s.knows x }

def State.step (s : State C P O) : Event C P O → State C P O
  | .move c p =>
    let s' := { s with loc := fun x => if x == c then p else s.loc x }
    s'.witness p (.at_ c p)
  | .take c o => ({ s with holder := fun x => if x == o then some c else s.holder x }).witness
      (s.loc c) (.holds c o)
  | .hide c o =>
    ({ s with holder := fun x => if x == o then none else s.holder x,
              objLoc := fun x => if x == o then s.loc c else s.objLoc x }).witness
      (s.loc c) (.objAt o (s.loc c))
  | .grab c v => { s with threats := (c, v) :: s.threats }
  | .shout _ _ => s
  | .tell _ d f => { s with knows := fun x => if x == d then f :: s.knows x else s.knows x }
  | .gag _ v => { s with gagged := fun x => if x == v then true else s.gagged x }
  | .drink c => { s with drunk := fun x => if x == c then true else s.drunk x }

/-! ## Time

Time is the position in the story: `s.run (es.take n)` is the state after the
first `n` events. "Was" quantifies over those prefixes. -/

def State.run (s : State C P O) : List (Event C P O) → State C P O
  | [] => s
  | e :: es => (s.step e).run es

/-- The state at time `n` of story `es` (after its first `n` events). -/
def State.at (s : State C P O) (es : List (Event C P O)) (n : Nat) : State C P O :=
  s.run (es.take n)

/-- `p` held at some time during `es`. -/
def Was (s : State C P O) (es : List (Event C P O)) (p : State C P O → Prop) : Prop :=
  ∃ n, n ≤ es.length ∧ p (s.at es n)

/-- `p` held at every time during `es`. -/
def Throughout (s : State C P O) (es : List (Event C P O)) (p : State C P O → Prop) : Prop :=
  ∀ n, n ≤ es.length → p (s.at es n)

/-! ## Character: a defeasible theory per action -/

inductive Atom (C : Type) where
  | trait (c : C) (t : Trait)
  | ally (c v : C)
  | near (c v : C)
  | threatens (a v : C)
  | drunk (c : C)
  | gagged (c : C)
  | shouts (c d : C)
  deriving DecidableEq, Repr

inductive RuleName | timidQuiet | brashLoud | drinkLoosens | gaggedSilent | protect
  deriving DecidableEq, Repr

/-- A rule's name, and the value it serves for its agent. -/
structure Label where
  name : RuleName
  value : Option Value := none
  deriving DecidableEq, Repr

def pos (a : Atom C) : Lit (Atom C) := ⟨a, true⟩
def neg (a : Atom C) : Lit (Atom C) := ⟨a, false⟩

def Persona.prefers (p : Persona C) (v w : Value) : Bool :=
  match p.values.idxOf? v, p.values.idxOf? w with
  | some i, some j => decide (i < j)
  | some _, none => true
  | _, _ => false

/-- Facts about `c`'s persona and situation relevant to `c` shouting at `d`. -/
def shoutFacts (s : State C P O) (c d : C) : List (Lit (Atom C)) :=
  let p := s.persona c
  p.traits.map (fun t => pos (.trait c t)) ++
  p.allies.flatMap (fun v =>
    [pos (.ally c v)] ++
    (if s.loc c == s.loc v then [pos (.near c v)] else []) ++
    (if s.threats.contains (d, v) then [pos (.threatens d v)] else [])) ++
  (if s.drunk c then [pos (.drunk c)] else []) ++
  (if s.gagged c then [pos (.gagged c)] else [])

def shoutRules (s : State C P O) (c d : C) : List (Rule (Atom C) Label) :=
  [ { label := ⟨.timidQuiet, some .safety⟩, kind := .defeasible,
      body := [pos (.trait c .timid)], head := neg (.shouts c d) },
    { label := ⟨.brashLoud, some .pride⟩, kind := .defeasible,
      body := [pos (.trait c .brash)], head := pos (.shouts c d) },
    { label := ⟨.drinkLoosens, none⟩, kind := .defeater,
      body := [pos (.drunk c)], head := pos (.shouts c d) },
    { label := ⟨.gaggedSilent, none⟩, kind := .strict,
      body := [pos (.gagged c)], head := neg (.shouts c d) } ] ++
  (s.persona c).allies.map fun v =>
    { label := ⟨.protect, some .loyalty⟩, kind := .defeasible,
      body := [pos (.threatens d v), pos (.ally c v), pos (.near c v)],
      head := pos (.shouts c d) }

/-- Strict rules beat the rest; otherwise the rule serving the value the
agent prefers wins. -/
def supFor (p : Persona C) (t r : Rule (Atom C) Label) : Bool :=
  (t.kind == .strict && r.kind != .strict) ||
  (t.kind != .strict && r.kind != .strict &&
   match t.label.value, r.label.value with
   | some v, some w => p.prefers v w
   | _, _ => false)

def shoutTheory (s : State C P O) (c d : C) : Theory (Atom C) Label :=
  { facts := shoutFacts s c d, rules := shoutRules s c d, sup := supFor (s.persona c) }

inductive InCharacter (s : State C P O) : Event C P O → Prop
  /-- nothing about `c` defeasibly rules out shouting at `d` -/
  | shout {c d} : NotDef (shoutTheory s c d) (neg (.shouts c d)) → InCharacter s (.shout c d)
  | other {e} : (∀ c d, e ≠ .shout c d) → InCharacter s e

/-- Stronger than in character: something about `c` supports the shout. -/
def Motivated (s : State C P O) (c d : C) : Prop := Def (shoutTheory s c d) (pos (.shouts c d))

inductive Valid : State C P O → List (Event C P O) → Prop
  | nil {s} : Valid s []
  | cons {s e es} : pre s e = true → InCharacter s e → Valid (s.step e) es → Valid s (e :: es)

/-! ## Deciding validity -/

def inCharB (s : State C P O) : Event C P O → Bool
  | .shout c d =>
    let T := shoutTheory s c d
    let k := certify T
    k.check T && k.steps.contains (neg (.shouts c d), false)
  | _ => true

def validB : State C P O → List (Event C P O) → Bool
  | _, [] => true
  | s, e :: es => pre s e && inCharB s e && validB (s.step e) es

omit [DecidableEq O] in
theorem inCharB_sound (s : State C P O) (e : Event C P O) (h : inCharB s e = true) :
    InCharacter s e := by
  cases e with
  | shout c d =>
    simp only [inCharB, Bool.and_eq_true, List.contains_iff_mem] at h
    exact .shout ((Cert.sound _ _ h.1).2 _ h.2)
  | _ => exact .other (by intros; simp)

theorem validB_sound : ∀ (s : State C P O) (es : List (Event C P O)),
    validB s es = true → Valid s es
  | _, [], _ => .nil
  | s, e :: es, h => by
    simp only [validB, Bool.and_eq_true] at h
    exact .cons h.1.1 (inCharB_sound s e h.1.2) (validB_sound _ es h.2)

omit [DecidableEq O] in
/-- An action whose opposite is defeasibly provable cannot appear in a valid story. -/
theorem not_inCharacter_of_def (s : State C P O) (c d : C)
    (h : Def (shoutTheory s c d) (neg (.shouts c d))) : ¬ InCharacter s (.shout c d) := by
  intro hi
  cases hi with
  | shout hn => exact coherent _ h hn
  | other hne => exact hne c d rfl

/-! ## Explanations -/

section
variable [ToString C] [ToString P] [ToString O]

def Value.str : Value → String
  | .safety => "safety" | .loyalty => "loyalty" | .pride => "pride"

def RuleName.str : RuleName → String
  | .timidQuiet => "timid people keep quiet" | .brashLoud => "brash people speak up"
  | .drinkLoosens => "drink loosens tongues" | .gaggedSilent => "the gagged cannot shout"
  | .protect => "protect a threatened ally"

def Fact.str : Fact C P O → String
  | .at_ c p => s!"{c} is at {p}" | .objAt o p => s!"the {o} is in the {p}"
  | .holds c o => s!"{c} holds the {o}"

def Event.str : Event C P O → String
  | .move c p => s!"{c} goes to the {p}" | .take c o => s!"{c} takes the {o}"
  | .hide c o => s!"{c} hides the {o}" | .grab c v => s!"{c} grabs {v}"
  | .shout c d => s!"{c} shouts at {d}" | .tell c d f => s!"{c} tells {d} that {f.str}"
  | .gag c v => s!"{c} gags {v}" | .drink c => s!"{c} drinks"

def Atom.str : Atom C → String
  | .trait c t => s!"{c} is {match t with | .timid => "timid" | .brash => "brash"}"
  | .ally c v => s!"{v} is {c}'s ally" | .near c v => s!"{c} is near {v}"
  | .threatens a v => s!"{a} threatens {v}" | .drunk c => s!"{c} is drunk"
  | .gagged c => s!"{c} is gagged" | .shouts c d => s!"{c} shouts at {d}"

private def ruleStr (r : Rule (Atom C) Label) : String :=
  let v := match r.label.value with | some v => s!" [{v.str}]" | none => ""
  s!"\"{r.label.name.str}\"{v}"

private def litStr (l : Lit (Atom C)) : String := (if l.pos then "" else "not: ") ++ l.atom.str

/-- Why a shout is or is not in character. -/
def shoutVerdict (s : State C P O) (c d : C) : String :=
  let T := shoutTheory s c d
  let k := certify T
  let q := pos (Atom.shouts c d)
  let applicable (r : Rule (Atom C) Label) := r.body.all fun a => k.status a == some true
  let fired (h : Lit (Atom C)) := (T.rules.filter fun r => r.head == h && applicable r).map ruleStr
  let repairs := (T.rules.filter fun r => r.head == q && r.kind != .defeater && !applicable r).map
    fun r => s!"{ruleStr r} needs {" and ".intercalate ((r.body.filter fun a => k.status a != some true).map litStr)}"
  if k.strict.contains q.neg then
    s!"impossible: {", ".intercalate (fired q.neg)}"
  else match k.status q.neg, k.status q with
  | some true, _ =>
    s!"out of character by {", ".intercalate (fired q.neg)}; to justify it, first establish: {"; or ".intercalate repairs}"
  | _, some true =>
    let over := fired q.neg
    s!"plausible by {", ".intercalate (fired q)}" ++
      (if over.isEmpty then "" else s!", overriding {", ".intercalate over}")
  | _, _ =>
    let why := T.rules.filter fun r => r.kind == .defeater && r.head == q && applicable r
    s!"in character ({", ".intercalate (why.map ruleStr)} lifts the default) but unmotivated; motivations: {"; or ".intercalate repairs}"

def preReason (s : State C P O) : Event C P O → String
  | .take c o => s!"the {o} is not where {c} is"
  | .hide c o => s!"{c} does not hold the {o}"
  | .grab c v => s!"{c} and {v} are not in the same place"
  | .shout c d => if s.gagged c then s!"{c} is gagged" else s!"{d} is not where {c} is"
  | .tell c d f =>
    if !(s.knows c).contains f then s!"{c} never learned that {f.str}"
    else if s.gagged c then s!"{c} is gagged" else s!"{d} is not where {c} is"
  | .gag c v => s!"{c} and {v} are not in the same place"
  | _ => "?"

/-- One line per event: a hard violation, the character verdict, or ok. -/
def explain : State C P O → List (Event C P O) → List String
  | _, [] => []
  | s, e :: es =>
    let line :=
      if !pre s e then s!"PLOT HOLE         {e.str}: {preReason s e}"
      else match e with
        | .shout c d =>
          (if inCharB s e then "ok                " else "OUT OF CHARACTER  ") ++
          s!"{e.str}: {shoutVerdict s c d}"
        | _ => s!"ok                {e.str}"
    line :: explain (s.step e) es
end

end LangLib.Scene
