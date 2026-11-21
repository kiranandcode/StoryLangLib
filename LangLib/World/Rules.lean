import LangLib.World.Argument

/-!
# Rules: an argument's inferences as ASPIC+ rules with Walton's schemes

`World/Argument` reads an `infer` move as a claim with reasons: supported
when every reason is granted. This file says more about the inference itself,
so a reader can ask whether the step from the reasons to the claim is any
good. Each inference is a `Rule`:

- its **kind**: `strict` (deductive or definitional: if the premises hold, so
  does the conclusion) or `defeasible` (the premises make the conclusion
  presumable, open to exceptions);
- its **scheme**, after Walton, Reed and Macagno, *Argumentation Schemes*
  (2008): argument from example to a generalisation, practical reasoning,
  abduction (inference to the best explanation), track record to capability,
  expert opinion, cause to effect, analogy, requirement matches capability,
  counterexample;
- its **premises**, each tagged with what it rests on when it is not itself
  the conclusion of another rule: a public fact, a worked example, a
  citation, the authors' word, a hedge, or a promise (something the authors
  will do);
- the scheme's **critical questions** (`Scheme.cqs`), which of them the text
  answers, and which a sceptical reader presses (the attack points).

**Attacks** follow ASPIC+ (Prakken 2010; Modgil and Prakken 2014): a
*rebutter* attacks a rule's conclusion, an *undercutter* attacks the
inference itself (the premises hold but do not license the conclusion here:
Spectre undercuts "the proof is correct, so the system is trustworthy"), an
*underminer* attacks a premise. Rebutting and undercutting only reach
defeasible rules (restricted rebut: a strict rule's conclusion stands if its
premises do), and an attack on a rule reaches every rule built on its
conclusion (an attack on a sub-argument is an attack on the argument).

**Labellings.** `labels` is the grounded labelling (Dung 1995; Caminada 2006)
of the text's rules under the text's own attacks; `scepticLabels` adds one
attacker for every pressed critical question. Both are least fixed points
computed by iteration, so the kernel decides them.

**Thin support** (`thin`): a generalisation from at most two examples, a
defeasible rule resting on a promise, or a defeasible rule whose premises all
rest on the authors' word. `bare` is the last condition for any rule: its
leaves are only the authors' word, hedges and promises.
-/

namespace LangLib.World.Argument

/-- Strict (deductive, definitional) or defeasible. -/
inductive RKind | strict | defeasible
  deriving DecidableEq, Repr

/-- Walton's schemes, plus the two strict ones. -/
inductive Scheme
  | deductive | definitional
  | exampleToGen | practical | abduction | trackRecord | expertOpinion
  | causeToEffect | analogy | requirement | counterexample
  /-- story schemes: seeing, being told, reading a sign, applying a world rule -/
  | perception | testimony | sign | ruleApp
  /-- no scheme read yet -/
  | unread
  deriving DecidableEq, Repr

inductive AttackKind | rebut | undercut | undermine
  deriving DecidableEq, Repr

/-- What a leaf premise rests on. -/
inductive Tag | fact | «example» | citation | authors | hedge | promise
  deriving DecidableEq, Repr

/-- Who puts a rule forward: the text, a position the text argues against,
or (for critical questions) the sceptical reader. -/
inductive Side | text | opponent
  deriving DecidableEq, Repr

def Scheme.name : Scheme → String
  | .deductive => "deduction" | .definitional => "definition"
  | .exampleToGen => "example to generalisation" | .practical => "practical reasoning"
  | .abduction => "abduction (best explanation)" | .trackRecord => "track record → capability"
  | .expertOpinion => "expert opinion" | .causeToEffect => "cause to effect"
  | .analogy => "analogy" | .requirement => "requirement matches capability"
  | .counterexample => "counterexample"
  | .perception => "perception" | .testimony => "witness testimony" | .sign => "sign"
  | .ruleApp => "rule application" | .unread => "unread"

/-- A scheme's critical questions, each with the attack it raises when
pressed (Walton, Reed and Macagno 2008, ch. 9, abridged). -/
def Scheme.cqs : Scheme → List (String × AttackKind)
  | .deductive | .definitional => []
  | .exampleToGen =>
    [("Is the example true?", .undermine),
     ("Is it typical of the class generalised over?", .undercut),
     ("Are there enough examples?", .undercut),
     ("Are there counterexamples?", .rebut),
     ("Did special circumstances make the example work?", .undercut)]
  | .practical =>
    [("Is the action possible (feasible)?", .undermine),
     ("Are there alternative actions that reach the goal?", .undercut),
     ("Is this the best of them?", .undercut),
     ("Does the goal conflict with other goals?", .rebut),
     ("What are the side effects and costs?", .rebut)]
  | .abduction =>
    [("Does the explanation account for the evidence?", .undercut),
     ("Is there a better or equally good explanation?", .rebut),
     ("How thorough was the search for alternatives?", .undercut),
     ("Should we wait for more evidence?", .undercut)]
  | .trackRecord =>
    [("Is the past work relevant to the new task?", .undercut),
     ("Is the record verifiable independently?", .undermine),
     ("Does the new task need something the record lacks (scale, new skills)?", .undercut)]
  | .expertOpinion =>
    [("Is the source an expert?", .undermine),
     ("Is it in the right field?", .undercut),
     ("What exactly did they assert?", .undermine),
     ("Is the source reliable (unbiased)?", .undercut),
     ("Do other experts agree?", .rebut),
     ("Is the assertion based on evidence?", .undercut)]
  | .causeToEffect =>
    [("How strong is the causal link?", .undercut),
     ("Is the evidence for it good enough?", .undermine),
     ("Could other factors interfere?", .undercut)]
  | .analogy =>
    [("Are the cases similar in the respects that matter?", .undercut),
     ("Is there a relevant difference?", .undercut),
     ("Is there a counter-analogy?", .rebut)]
  | .requirement =>
    [("Is the list of requirements complete?", .undercut),
     ("Is each capability demonstrated?", .undermine),
     ("Do others have the same capabilities?", .rebut)]
  | .counterexample =>
    [("Is the counterexample real?", .undermine),
     ("Does it fall within the generalisation's scope?", .undercut),
     ("Can the generalisation be repaired to exclude it?", .rebut)]
  | .perception =>
    [("Was the perceiver in a position to see it?", .undermine),
     ("Could the perception be mistaken (conditions, deception)?", .undercut)]
  | .testimony =>
    [("Was the witness in a position to know?", .undermine),
     ("Is the witness honest (no motive to deceive)?", .undercut),
     ("Is the testimony consistent with other evidence?", .rebut)]
  | .sign =>
    [("Is the sign reliable for this conclusion?", .undercut),
     ("Is there another cause of the sign?", .rebut)]
  | .ruleApp | .unread => []

/-- The part a premise plays in its scheme (Walton's premise names, abridged).
A rule's premises are typed by these: a scheme allows some slots and requires
some (`Scheme.spec`). -/
inductive Slot
  | premise | definition | general | instance | condition | limit
  | goal | problem | means | feasible | who
  | needs | provides
  | case | result
  | observed | explanation | rival | principle
  | cause | effect
  | source | target | similarity
  | pastWork | selfAssessment
  | expert | perceived | said | witness | access | sign
  deriving DecidableEq, Repr

def Slot.name : Slot → String
  | .premise => "premise" | .definition => "definition" | .general => "general claim" | .instance => "instance"
  | .condition => "condition" | .limit => "but" | .goal => "goal" | .problem => "problem" | .means => "means"
  | .feasible => "feasible" | .who => "who" | .needs => "needs" | .provides => "provides" | .case => "case"
  | .result => "result" | .observed => "observed" | .explanation => "explanation" | .rival => "rival"
  | .principle => "principle" | .cause => "cause" | .effect => "effect" | .source => "source case"
  | .target => "target case" | .similarity => "alike because" | .pastWork => "past work"
  | .selfAssessment => "self-assessment" | .expert => "expert" | .perceived => "perceived" | .said => "said"
  | .witness => "witness" | .access => "access" | .sign => "sign"

/-- What each scheme allows and what it requires. A required slot nobody fills
is an *enthymeme*: a premise the argument needs and the text leaves unstated. -/
def Scheme.spec : Scheme → List Slot × List Slot
  | .deductive => ([.premise, .general, .instance, .condition, .definition], [])
  | .definitional => ([.definition, .premise], [.definition])
  | .exampleToGen => ([.case, .result, .cause, .principle, .general], [.case])
  | .practical => ([.goal, .problem, .means, .feasible, .who, .limit, .needs], [.goal, .means])
  | .abduction => ([.observed, .explanation, .rival, .principle, .general], [.observed, .rival])
  | .trackRecord => ([.pastWork, .selfAssessment, .similarity], [.pastWork])
  | .expertOpinion => ([.expert, .said, .access], [.expert, .said])
  | .causeToEffect => ([.cause, .effect, .condition, .limit, .general], [.cause])
  | .analogy => ([.source, .target, .similarity], [.source, .target, .similarity])
  | .requirement => ([.needs, .provides, .limit, .general], [.needs, .provides])
  | .counterexample => ([.case, .general], [.case, .general])
  | .perception => ([.perceived, .access, .condition], [.perceived])
  | .testimony => ([.said, .witness, .access], [.said])
  | .sign => ([.sign, .general], [.sign])
  | .ruleApp => ([.condition], [.condition])
  | .unread => ([], [])

/-- At most this many premises to a rule; past it, group them into sub-rules. -/
def maxFanIn : Nat := 6

/-- An inference, named `id`. A premise that some rule concludes is a
sub-argument; any other premise is a leaf and its tag says what it rests on. -/
structure Rule (T : Type) where
  id : T
  concl : T
  premises : List (T × Tag)
  kind : RKind
  scheme : Scheme
  side : Side := .text
  /-- critical questions (indices into `scheme.cqs`) the text answers -/
  answered : List Nat := []
  /-- open critical questions a sceptical reader presses: attack points -/
  pressed : List Nat := []
  /-- the slot each premise fills -/
  slots : List (T × Slot) := []
  deriving DecidableEq, Repr

/-- `src` attacks `tgt` (rule ids); an underminer names the premise `on`. -/
structure RAttack (T : Type) where
  src : T
  tgt : T
  how : AttackKind
  on : Option T := none
  deriving DecidableEq, Repr

/-- What a labelling ranges over: the rules, and one sceptic per pressed
critical question. -/
inductive ANode (T : Type) | rule (id : T) | cq (r : T) (i : Nat)
  deriving DecidableEq, Repr

inductive Lab | «in» | out | undec
  deriving DecidableEq, Repr

variable {T : Type} [DecidableEq T]

def ruleOf (rs : List (Rule T)) (i : T) : Option (Rule T) := rs.find? (·.id == i)

/-- The rule that concludes `p`, if any (a sub-argument for the premise). -/
def concluder (rs : List (Rule T)) (p : T) : Option (Rule T) := rs.find? (·.concl == p)

/-- ASPIC+'s restrictions: rebutters and undercutters reach only defeasible
rules; an underminer names a leaf premise of its target that is not a fact. -/
def attackOk (rs : List (Rule T)) (a : RAttack T) : Bool :=
  (ruleOf rs a.src).isSome && match ruleOf rs a.tgt with
  | none => false
  | some r => match a.how with
    | .rebut | .undercut => r.kind == .defeasible
    | .undermine => match a.on with
      | some p => r.premises.any (fun (q, t) => q == p && t != .fact) && (concluder rs p).isNone
      | none => false

/-- The rules `r` is built on, `r` included (sub-arguments, to depth `fuel`). -/
def subRules (rs : List (Rule T)) : Nat → Rule T → List T
  | 0, r => [r.id]
  | n + 1, r => r.id :: r.premises.flatMap fun (p, _) =>
      match concluder rs p with
      | some s => subRules rs n s
      | none => []

/-- The rules an attack on `tgt` reaches: `tgt` and every rule built on it. -/
def reached (rs : List (Rule T)) (tgt : T) : List T :=
  (rs.filter fun r => (subRules rs rs.length r).contains tgt).map (·.id)

/-- The attack relation over nodes: each well-formed attack reaches every
rule built on its target. -/
def attackPairs (rs : List (Rule T)) (as : List (RAttack T)) : List (ANode T × ANode T) :=
  (as.filter (attackOk rs)).flatMap fun a => (reached rs a.tgt).map fun r => (.rule a.src, .rule r)

/-- One sceptic per pressed critical question; a rebutting or undercutting
one only reaches a defeasible rule. -/
def scepticPairs (rs : List (Rule T)) : List (ANode T × ANode T) :=
  rs.flatMap fun r => (r.pressed.filter fun i =>
      i < r.scheme.cqs.length && (r.kind == .defeasible ||
        ((r.scheme.cqs[i]?).map (·.2) == some .undermine))).flatMap fun i =>
    (reached rs r.id).map fun r' => (.cq r.id i, .rule r')

def labOf (lab : List (ANode T × Lab)) (x : ANode T) : Lab := ((lab.find? (·.1 == x)).map (·.2)).getD .undec

/-- One round: a node is in when all its attackers are out, out when one is in. -/
def labRound (att : List (ANode T × ANode T)) (lab : List (ANode T × Lab)) : List (ANode T × Lab) :=
  lab.map fun (x, l) =>
    if l != .undec then (x, l) else
    let by_ := (att.filter (·.2 == x)).map (·.1)
    if by_.all (labOf lab · == .out) then (x, .in)
    else if by_.any (labOf lab · == .in) then (x, .out) else (x, .undec)

/-- The grounded labelling: from all undecided, `nodes.length + 1` rounds. -/
def grounded (nodes : List (ANode T)) (att : List (ANode T × ANode T)) : List (ANode T × Lab) :=
  (List.range (nodes.length + 1)).foldl (fun lab _ => labRound att lab) (nodes.map (·, .undec))

/-- The grounded labelling of the rules under the text's own attacks. -/
def labels (rs : List (Rule T)) (as : List (RAttack T)) : List (T × Lab) :=
  let lab := grounded (rs.map (.rule ·.id)) (attackPairs rs as)
  rs.map fun r => (r.id, labOf lab (.rule r.id))

/-- The same, with every pressed critical question as an unanswered attacker. -/
def scepticLabels (rs : List (Rule T)) (as : List (RAttack T)) : List (T × Lab) :=
  let sp := scepticPairs rs
  let nodes := rs.map (.rule ·.id) ++ (sp.map (·.1)).eraseDups
  let lab := grounded nodes (attackPairs rs as ++ sp)
  rs.map fun r => (r.id, labOf lab (.rule r.id))

/-- The tags of a rule's leaf premises, through its sub-arguments. -/
def leafTags (rs : List (Rule T)) : Nat → Rule T → List Tag
  | 0, r => r.premises.map (·.2)
  | n + 1, r => r.premises.flatMap fun (p, t) =>
      match concluder rs p with
      | some s => leafTags rs n s
      | none => [t]

/-- The authors' word alone: every leaf is the authors' word, a hedge or a promise. -/
def bare (rs : List (Rule T)) (r : Rule T) : Bool :=
  (leafTags rs rs.length r).all fun t => t == .authors || t == .hedge || t == .promise

/-- Why a defeasible link's support is thin. -/
inductive Thin | fewExamples (n : Nat) | onPromise | authorsWord
  deriving DecidableEq, Repr

/-- The evidence under a rule: its leaves that are examples or citations. -/
def evidence (rs : List (Rule T)) (r : Rule T) : Nat :=
  ((leafTags rs rs.length r).filter fun t => t == .«example» || t == .citation).length

def thin (rs : List (Rule T)) (r : Rule T) : List Thin :=
  if r.kind == .strict then [] else
  (if r.scheme == .exampleToGen && evidence rs r ≤ 2 then [.fewExamples (evidence rs r)] else []) ++
  (if r.premises.any (fun (p, t) => t == .promise && (concluder rs p).isNone) then [.onPromise] else []) ++
  (if bare rs r then [.authorsWord] else [])

/-- The text's rules whose conclusion rests on the authors' word alone. -/
def bareRules (rs : List (Rule T)) : List T :=
  ((rs.filter (·.side == .text)).filter (bare rs)).map (·.id)

/-- Leaf premises of the text's rules that rest on the authors' word or a
hedge: claims nothing in the text supports. -/
def bareLeaves (rs : List (Rule T)) : List T :=
  ((rs.filter (·.side == .text)).flatMap fun r => r.premises.filterMap fun (p, t) =>
    if (concluder rs p).isNone && (t == .authors || t == .hedge) then some p else none).eraseDups

/-- The text's rules with thin support, and why. -/
def thinRules (rs : List (Rule T)) : List (T × List Thin) :=
  ((rs.filter (·.side == .text)).map fun r => (r.id, thin rs r)).filter (!·.2.isEmpty)

/-- Critical questions left open: neither answered by the text. -/
def openCqs (r : Rule T) : List Nat :=
  (List.range r.scheme.cqs.length).filter (!r.answered.contains ·)

/-- What can be wrong with a rule's shape: a premise with no slot, a slot its
scheme does not allow, too many premises, no premises, or no scheme read. -/
inductive Fault (T : Type) | unslotted (p : T) | illegal (p : T) (s : Slot) | fanIn (n : Nat) | empty | unread
  deriving DecidableEq, Repr

def slotOf (r : Rule T) (p : T) : Option Slot := (r.slots.find? (·.1 == p)).map (·.2)

def faults (r : Rule T) : List (Fault T) :=
  (if r.scheme == .unread then [.unread] else
    r.premises.filterMap fun (p, _) => match slotOf r p with
      | none => some (.unslotted p)
      | some s => if r.scheme.spec.1.contains s then none else some (.illegal p s)) ++
  (if r.premises.length > maxFanIn then [.fanIn r.premises.length] else []) ++
  (if r.premises.isEmpty && r.kind == .defeasible then [.empty] else [])

/-- Required slots no premise fills: what the text leaves unstated. -/
def enthymemes (r : Rule T) : List Slot :=
  r.scheme.spec.2.filter fun s => !(r.premises.any fun (p, _) => slotOf r p == some s)

/-- Every rule is well shaped: each premise fills a slot its scheme allows, and
no rule has more than `maxFanIn` premises. (Enthymemes are findings about the
text, not faults of the reading.) -/
def Shaped (rs : List (Rule T)) : Prop := rs.all (fun r => (faults r).isEmpty) = true

instance (rs : List (Rule T)) : Decidable (Shaped rs) := by unfold Shaped; infer_instance

/-- The text's rules with unstated required premises. -/
def enthymemeRules (rs : List (Rule T)) : List (T × List Slot) :=
  ((rs.filter (·.side == .text)).map fun r => (r.id, enthymemes r)).filter (!·.2.isEmpty)

/-- Every attack is well formed and every pressed question is open. -/
def RulesOk (rs : List (Rule T)) (as : List (RAttack T)) : Prop :=
  as.all (attackOk rs) = true ∧ rs.all (fun r => r.pressed.all (openCqs r).contains) = true

instance (rs : List (Rule T)) (as : List (RAttack T)) : Decidable (RulesOk rs as) := by
  unfold RulesOk; infer_instance

namespace RToy
/-- Spectre: the verified-OS argument, undercut by a counterexample. -/
inductive Tm | proofOk | trusted | spectre | modelWrong | scienceNeeded | r0 | r1 | r2
  deriving DecidableEq, Repr


def rs : List (Rule Tm) :=
  [ { id := .r0, concl := .trusted, premises := [(.proofOk, .fact)], kind := .defeasible,
      scheme := .causeToEffect, side := .opponent },
    { id := .r1, concl := .modelWrong, premises := [(.spectre, .«example»)], kind := .defeasible,
      scheme := .counterexample, answered := [0, 1], slots := [(.spectre, .case)] },
    { id := .r2, concl := .scienceNeeded, premises := [(.modelWrong, .authors)], kind := .defeasible,
      scheme := .exampleToGen, pressed := [2], slots := [(.modelWrong, .case)] } ]

def as : List (RAttack Tm) := [{ src := .r1, tgt := .r0, how := .undercut }]

theorem ok : RulesOk rs as := by decide +kernel
/-- Spectre's undercutter is in, so "proof ⇒ trusted" is out. -/
theorem lab : labels rs as = [(.r0, .out), (.r1, .in), (.r2, .in)] := by decide +kernel
/-- Pressing "are there enough examples?" takes the generalisation out. -/
theorem sceptic : scepticLabels rs as = [(.r0, .out), (.r1, .in), (.r2, .out)] := by decide +kernel
/-- One example is thin support for a generalisation. -/
theorem thinR2 : thinRules rs = [(.r2, [.fewExamples 1])] := by decide +kernel
def strictR0 : Rule Tm :=
  { id := .r0, concl := .trusted, premises := [(.proofOk, .fact)], kind := RKind.strict, scheme := .deductive }
def r1' : Rule Tm := { id := .r1, concl := .modelWrong, premises := [], kind := .defeasible, scheme := .counterexample }
/-- r0 gives its premise no slot; r1's counterexample names no general claim (unstated). -/
theorem shape : rs.map faults = [[.unslotted .proofOk], [], []] ∧
    enthymemeRules rs = [(.r1, [.general])] := by decide +kernel
/-- r2 rests on r1, so the toy has no bare leaf. -/
theorem bareR2 : bareLeaves rs = [] := by decide +kernel
/-- A strict rule cannot be rebutted. -/
theorem noRebutStrict : attackOk [strictR0, r1'] { src := .r1, tgt := .r0, how := .rebut } = false := by
  decide +kernel
end RToy

end LangLib.World.Argument
