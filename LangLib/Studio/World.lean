import LangLib.World.Goals

/-!
# A story world from data

The worked examples each declare their own characters, places and state. The
Studio needs worlds that an agent writes as data (`stories/<name>/story.json`),
checked without recompiling Lean. This file is one world, parameterised by a
`Spec`: the cast (with personas), places, objects, story-specific atoms (with
their truth, exclusion groups and lore), plans, and the opening state. It uses
the same modules as the examples (space, minds, relationships and consent,
dialogue, goals), so a story checked by the CLI and a story proved by `decide`
in a story's Lean file run the same definitions.

* Characters, places and objects are numbers wrapped in `Ch s`, `Pl s`, `Ob s`,
  so the cast of `s` is a type-level fact (`Cast (Ch s)`).
* `Fact` is spec-independent (ids as numbers); `SFact s` wraps it so that its
  lore and exclusions come from `s`.
* `Ev` is the surface event syntax stories are written in; `Ev.toE` reads it
  into the module events.
-/

namespace LangLib.Studio
open LangLib.World

/-- Facts, with characters, places and objects by number. -/
inductive Fact where
  | at_ (c p : Nat)
  | objAt (o p : Nat)
  | holds (c o : Nat)
  | did (a b : Nat) (x : Act)
  | atom (i : Nat)
  deriving DecidableEq, Repr, BEq

/-- Surface events: what a story file lists, one per clause. -/
inductive Ev where
  | move (c p : Nat) | take (c o : Nat) | drop (c o : Nat) | give (c d o : Nat)
  | tell (c d : Nat) (l : Fact × Bool) | whisper (c d : Nat) (l : Fact × Bool)
  | lie (c d : Nat) (l : Fact × Bool)
  | notice (c : Nat) (l : Fact × Bool) (e : Evid Nat) | realise (c : Nat) (l : Fact × Bool)
  | flirt (a b : Nat) | confide (a b : Nat) | argue (a b : Nat)
  | askAct (a b : Nat) (x : Act) | agree (b a : Nat) (x : Act) | withdraw (b a : Nat) (x : Act)
  | act (a b : Nat) (x : Act)
  | ask (c d : Nat) (f : Fact) | answer (d c : Nat) (l : Fact × Bool)
  | hint (c d : Nat) (l : Fact × Bool) | sarcasm (c d : Nat) (l : Fact × Bool)
  | promise (c d : Nat) (l : Fact × Bool) | request (c d : Nat) (l : Fact × Bool)
  | adopt (c : Nat) (g : Fact × Bool) | dropGoal (c : Nat) (g : Fact × Bool)
  | intend (c : Nat) (plan : Nat) | abandon (c : Nat) (g : Fact × Bool)
  deriving DecidableEq, Repr, BEq

structure CharSpec where
  id : String
  name : String
  pron : String := "she"
  traits : List Trait := []
  values : List Value := []
  deriving Repr, DecidableEq

structure AtomSpec where
  id : String
  label : String
  truth : Bool
  /-- atoms in the same non-empty group exclude each other -/
  group : String := ""
  deriving Repr, DecidableEq

structure PlanSpec where
  id : String
  agent : Nat
  goal : Fact × Bool
  steps : List Ev
  deriving Repr, DecidableEq

structure Spec where
  chars : List CharSpec
  places : List String
  objects : List String
  atoms : List AtomSpec
  lore : List (List (Fact × Bool) × (Fact × Bool)) := []
  plans : List PlanSpec := []
  /-- characters whose opening place is stated: (character, place) -/
  startAt : List (Nat × Nat) := []
  /-- objects lying somewhere: (object, place) -/
  startObjAt : List (Nat × Nat) := []
  /-- objects held: (object, character) -/
  startHeld : List (Nat × Nat) := []
  /-- (from, to, dimension, level) -/
  bonds : List (Nat × Nat × Dim × Nat) := []
  /-- what characters know at the start (their own knowledge) -/
  knows : List (Nat × (Fact × Bool)) := []
  goals : List (Nat × (Fact × Bool)) := []
  deriving Repr, DecidableEq

structure Ch (s : Spec) where i : Nat deriving DecidableEq, Repr
structure Pl (s : Spec) where i : Nat deriving DecidableEq, Repr
structure Ob (s : Spec) where i : Nat deriving DecidableEq, Repr
structure SFact (s : Spec) where f : Fact deriving DecidableEq, Repr

variable {s : Spec}

instance : Cast (Ch s) := ⟨(List.range s.chars.length).map (⟨·⟩)⟩

inductive A (s : Spec) where
  | space (x : SpaceEv (Ch s) (Pl s) (Ob s))
  | mind (x : MindEv (Ch s) (SFact s))
  | social (x : SocialEv (Ch s))
  | dialogue (x : DialogueEv (Ch s) (SFact s))
  deriving DecidableEq, Repr

inductive E (s : Spec) where
  | action (x : A s)
  | goal (x : GoalEv (Ch s) (SFact s) (A s))
  deriving DecidableEq, Repr

structure W (s : Spec) where
  loc : Ch s → Pl s
  known : List (Ch s)
  holder : Ob s → Option (Ch s)
  objLoc : Ob s → Pl s
  objKnown : List (Ob s)
  beliefs : Ch s → List (Held (Ch s) (SFact s))
  bond : Ch s → Ch s → Dim → Nat
  consent : List (Ch s × Ch s × Act) := []
  questions : List (Ch s × Ch s × SFact s) := []
  promises : List (Ch s × Ch s × (SFact s × Bool)) := []
  requests : List (Ch s × Ch s × (SFact s × Bool)) := []
  goals : Ch s → List (SFact s × Bool)
  plans : Ch s → List (Plan (A s) (SFact s)) := fun _ => []
  clock : Nat := 0

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-! ## Facts -/

def Fact.supersedes (s : Spec) : Fact → Fact → Bool
  | .at_ c _, .at_ c' _ => c == c'
  | .objAt o _, .objAt o' _ | .objAt o _, .holds _ o' | .holds _ o, .holds _ o'
  | .holds _ o, .objAt o' _ => o == o'
  | .atom i, .atom j =>
    i != j && match s.atoms[i]?, s.atoms[j]? with
      | some a, some b => a.group != "" && a.group == b.group
      | _, _ => false
  | _, _ => false

def Fact.fluent : Fact → Bool
  | .at_ .. | .objAt .. | .holds .. => true
  | _ => false

instance : Supersedes (SFact s) := ⟨fun a b => a.f.supersedes s b.f⟩
instance : Fluent (SFact s) := ⟨fun a => a.f.fluent⟩
instance : Lore (SFact s) :=
  ⟨s.lore.map fun (body, (h, b)) => ⟨body.map fun (f, p) => (⟨f⟩, p), (⟨h⟩, b)⟩⟩

instance : Inject (SpaceFact (Ch s) (Pl s) (Ob s)) (SFact s) where
  inj | .at_ c p => ⟨.at_ c.i p.i⟩ | .objAt o p => ⟨.objAt o.i p.i⟩ | .holds c o => ⟨.holds c.i o.i⟩
instance : Inject (SocialFact (Ch s)) (SFact s) where
  inj | .did a b x => ⟨.did a.i b.i x⟩

/-! ## The world's lenses -/

instance : HasSpace (W s) (Ch s) (Pl s) (Ob s) where
  loc := W.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder := W.holder
  setHolder w o h := { w with holder := upd w.holder o h }
  objLoc := W.objLoc
  setObjLoc w o p := { w with objLoc := upd w.objLoc o p }

instance : PartialLoc (W s) (Ch s) where
  locKnown w c := w.known.contains c
  assumeAt w a b := { w with loc := upd w.loc a (w.loc b), known := a :: w.known }
  markLoc w c := { w with known := c :: w.known }

instance : PartialObj (W s) (Ob s) where
  objKnown w o := w.objKnown.contains o
  markObj w o := { w with objKnown := o :: w.objKnown }

instance : HasMinds (W s) (Ch s) (SFact s) :=
  ⟨W.beliefs, fun w c bs => { w with beliefs := upd w.beliefs c bs }⟩

instance : HasBonds (W s) (Ch s) where
  bond := W.bond
  setBond w a b k n := { w with bond := fun x y j => if x = a ∧ y = b ∧ j = k then n else w.bond x y j }
  consent := W.consent
  setConsent w cs := { w with consent := cs }

def Spec.persona (s : Spec) (c : Nat) : Persona :=
  match s.chars[c]? with
  | some cs => { traits := cs.traits, values := cs.values }
  | none => { traits := [], values := [] }

instance : HasPersona (W s) (Ch s) := ⟨fun _ c => s.persona c.i⟩

instance : HasDialogue (W s) (Ch s) (SFact s) where
  questions := W.questions
  setQuestions w q := { w with questions := q }
  promises := W.promises
  setPromises w p := { w with promises := p }
  requests := W.requests
  setRequests w r := { w with requests := r }

instance : HasGoals (W s) (Ch s) (SFact s) (A s) where
  goals := W.goals
  setGoals w c g := { w with goals := upd w.goals c g }
  plans := W.plans
  setPlans w c p := { w with plans := upd w.plans c p }

instance : Clock (W s) := ⟨W.clock, fun w => { w with clock := w.clock + 1 }⟩

def Fact.truth (w : W s) : Fact → Bool
  | .at_ c p => w.loc ⟨c⟩ == ⟨p⟩
  | .objAt o p => w.holder ⟨o⟩ == none && w.objLoc ⟨o⟩ == ⟨p⟩
  | .holds c o => w.holder ⟨o⟩ == some ⟨c⟩
  | .did _ _ _ => true
  | .atom i => (s.atoms[i]?.map (·.truth)).getD false

instance : Truth (W s) (SFact s) := ⟨fun w f => f.f.truth w⟩
instance : Credence (W s) (Ch s) (SFact s) := socialCredence
instance : Rapport (W s) (Ch s) := bondRapport

/-! ## Events: injections and dispatch -/

instance : Inject (SpaceEv (Ch s) (Pl s) (Ob s)) (A s) := ⟨.space⟩
instance : Inject (MindEv (Ch s) (SFact s)) (A s) := ⟨.mind⟩
instance : Inject (SocialEv (Ch s)) (A s) := ⟨.social⟩
instance : Inject (DialogueEv (Ch s) (SFact s)) (A s) := ⟨.dialogue⟩
instance : Inject (A s) (E s) := ⟨.action⟩
instance : Inject (GoalEv (Ch s) (SFact s) (A s)) (E s) := ⟨.goal⟩

instance : Domain (W s) (A s) where
  ok w | .space x => Domain.ok w x | .mind x => Domain.ok w x
       | .social x => Domain.ok w x | .dialogue x => Domain.ok w x
  ok3 w | .space x => Domain.ok3 w x | .mind x => Domain.ok3 w x
        | .social x => Domain.ok3 w x | .dialogue x => Domain.ok3 w x
  why w | .space x => Domain.why w x | .mind x => Domain.why w x
        | .social x => Domain.why w x | .dialogue x => Domain.why w x
  step w | .space x => Domain.step w x | .mind x => Domain.step w x
         | .social x => Domain.step w x | .dialogue x => Domain.step w x

instance : Domain (W s) (E s) where
  ok w | .action x => Domain.ok w x | .goal x => Domain.ok w x
  ok3 w | .action x => Domain.ok3 w x | .goal x => Domain.ok3 w x
  why w | .action x => Domain.why w x | .goal x => Domain.why w x
  step w | .action x => Domain.step w x | .goal x => Domain.step w x

instance : Observable (W s) (A s) (SFact s) (Pl s) where
  seen w | .space x => Observable.seen w x | .social x => Observable.seen w x | _ => none

instance : Observable (W s) (E s) (SFact s) (Pl s) where
  seen w | .action x => Observable.seen w x | .goal _ => none

/-- Who must have a reason: movers, takers and givers, and whoever initiates an
intimate act. Talk (flirting, confiding, asking, agreeing) is expressive and
needs no goal. -/
instance : Purpose (W s) (A s) (Ch s) (SFact s) where
  agent | .space x => Purpose.agent (W := W s) (Φ := SFact s) x
        | .social (.act a _ _) => some a
        | _ => none
  effects w | .space x => Purpose.effects (C := Ch s) w x
            | .social x => Purpose.effects (C := Ch s) w x
            | _ => []

instance : Purpose (W s) (E s) (Ch s) (SFact s) where
  agent | .action x => Purpose.agent (W := W s) (Φ := SFact s) x | .goal _ => none
  effects w | .action x => Purpose.effects (C := Ch s) w x | .goal _ => []

/-! ## From the surface syntax -/

def lit (l : Fact × Bool) : SFact s × Bool := (⟨l.1⟩, l.2)

def Evid.toCh : Evid Nat → Evid (Ch s)
  | .self => .self | .seen => .seen | .sensed => .sensed | .inferred => .inferred
  | .assumed => .assumed | .told c => .told ⟨c⟩ | .relayed c => .relayed ⟨c⟩ | .rumour => .rumour

/-- An action (anything but a goal event); goal events give `none`. -/
def Ev.toA : Ev → Option (A s)
  | .move c p => some (.space (.move ⟨c⟩ ⟨p⟩))
  | .take c o => some (.space (.take ⟨c⟩ ⟨o⟩))
  | .drop c o => some (.space (.drop ⟨c⟩ ⟨o⟩))
  | .give c d o => some (.space (.give ⟨c⟩ ⟨d⟩ ⟨o⟩))
  | .tell c d l => some (.mind (.tell ⟨c⟩ ⟨d⟩ (lit l)))
  | .whisper c d l => some (.mind (.whisper ⟨c⟩ ⟨d⟩ (lit l)))
  | .lie c d l => some (.mind (.lie ⟨c⟩ ⟨d⟩ (lit l)))
  | .notice c l e => some (.mind (.notice ⟨c⟩ (lit l) (Evid.toCh e)))
  | .realise c l => some (.mind (.realise ⟨c⟩ (lit l)))
  | .flirt a b => some (.social (.flirt ⟨a⟩ ⟨b⟩))
  | .confide a b => some (.social (.confide ⟨a⟩ ⟨b⟩))
  | .argue a b => some (.social (.argue ⟨a⟩ ⟨b⟩))
  | .askAct a b x => some (.social (.ask ⟨a⟩ ⟨b⟩ x))
  | .agree b a x => some (.social (.agree ⟨b⟩ ⟨a⟩ x))
  | .withdraw b a x => some (.social (.withdraw ⟨b⟩ ⟨a⟩ x))
  | .act a b x => some (.social (.act ⟨a⟩ ⟨b⟩ x))
  | .ask c d f => some (.dialogue (.ask ⟨c⟩ ⟨d⟩ ⟨f⟩))
  | .answer d c l => some (.dialogue (.answer ⟨d⟩ ⟨c⟩ (lit l)))
  | .hint c d l => some (.dialogue (.hint ⟨c⟩ ⟨d⟩ (lit l)))
  | .sarcasm c d l => some (.dialogue (.sarcasm ⟨c⟩ ⟨d⟩ (lit l)))
  | .promise c d l => some (.dialogue (.promise ⟨c⟩ ⟨d⟩ (lit l)))
  | .request c d l => some (.dialogue (.request ⟨c⟩ ⟨d⟩ (lit l)))
  | _ => none

def Spec.plan (s : Spec) (k : Nat) : Plan (A s) (SFact s) :=
  match s.plans[k]? with
  | some p => { goal := lit p.goal, steps := p.steps.filterMap Ev.toA }
  | none => { goal := (⟨.atom 0⟩, true), steps := [] }

def Ev.toE (s : Spec) : Ev → E s
  | .adopt c g => .goal (.adopt ⟨c⟩ (lit g))
  | .dropGoal c g => .goal (.drop ⟨c⟩ (lit g))
  | .intend c k => .goal (.intend ⟨c⟩ (s.plan k))
  | .abandon c g => .goal (.abandon ⟨c⟩ (lit g))
  | e => match Ev.toA e with
    | some a => .action a
    | none => .goal (.drop ⟨0⟩ (⟨.atom 0⟩, true))

def own (l : Fact × Bool) : Held (Ch s) (SFact s) :=
  { b := ofLit (lit l), src := .self, rank := 10, stamp := 0, up := .hard }

def lookup {β : Type} (xs : List (Nat × β)) (k : Nat) : Option β :=
  (xs.find? (·.1 == k)).map (·.2)

/-- The opening state. -/
def Spec.start (s : Spec) : W s where
  -- characters whose place the text has not given are offstage (a place past
  -- the story's own), so they witness and overhear nothing until they appear
  loc c := ⟨(lookup s.startAt c.i).getD s.places.length⟩
  known := s.startAt.map (⟨·.1⟩)
  holder o := (lookup s.startHeld o.i).map (⟨·⟩)
  objLoc o := ⟨(lookup s.startObjAt o.i).getD 0⟩
  objKnown := (s.startObjAt ++ s.startHeld).map (⟨·.1⟩)
  beliefs c := (s.knows.filter (·.1 == c.i)).map fun (_, l) => own l
  bond a b k := ((s.bonds.find? fun (x, y, j, _) => x == a.i && y == b.i && j == k).map
    (·.2.2.2)).getD 0
  goals c := (s.goals.filter (·.1 == c.i)).map fun (_, g) => lit g

end LangLib.Studio
