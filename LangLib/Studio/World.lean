import LangLib.World.Goals
import LangLib.Studio.Place

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
* Atoms marked `state` are fluents that events change: `make c l` (a
  character brings it about, so needs a reason, and must be where the thing it
  is about is) and `become l` (it comes about by itself, like the rain
  stopping). Other atoms are fixed truths.
* The setting (`Place.lean`) rides along in the spec: place kinds, fixtures,
  scenery, the words for plot objects, and the layout.
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
  | make (c : Nat) (a : Nat) (v : Bool) | become (a : Nat) (v : Bool)
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
  /-- a state events change (`make`, `become`); `truth` is its opening value -/
  state : Bool := false
  /-- the place or thing the state is about (whoever changes it must be there) -/
  about : Option Spot := none
  /-- what sort of fact it is: "weather", "light", "sound", "condition", ... A
  clause that names weather, light or sound must be judged by a fact of that kind. -/
  kind : String := ""
  /-- perceptible where it is (its `about`'s place; weather: any outdoor place):
  when the point-of-view character arrives and finds it new to her, the
  paragraph must register it -/
  perceptible : Bool := false
  /-- the characters it is about (for holding the prose's clauses to it) -/
  who : List Nat := []
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
  /-- what kind of place each place is, by place index -/
  placeInfo : List (Nat × PlaceInfo) := []
  /-- fixtures and scenery -/
  things : List ThingSpec := []
  /-- the nouns that name each plot object -/
  objWords : List (Nat × List String) := []
  /-- whose each plot object is ("his keys"), by object index -/
  objOwner : List (Nat × Nat) := []
  layout : List Fixed := []
  /-- the point-of-view character, when the story keeps to one -/
  pov : Option Nat := none
  deriving Repr, DecidableEq

structure Ch (s : Spec) where i : Nat deriving DecidableEq, Repr
structure Pl (s : Spec) where i : Nat deriving DecidableEq, Repr
structure Ob (s : Spec) where i : Nat deriving DecidableEq, Repr
structure SFact (s : Spec) where f : Fact deriving DecidableEq, Repr

variable {s : Spec}

/-- State changes: `make c a v` (c sets atom `a` to `v`), `become a v`. -/
inductive StEv (s : Spec) where
  | make (c : Ch s) (a : Nat) (v : Bool)
  | become (a : Nat) (v : Bool)
  deriving DecidableEq, Repr

instance : Cast (Ch s) := ⟨(List.range s.chars.length).map (⟨·⟩)⟩

inductive A (s : Spec) where
  | space (x : SpaceEv (Ch s) (Pl s) (Ob s))
  | mind (x : MindEv (Ch s) (SFact s))
  | social (x : SocialEv (Ch s))
  | dialogue (x : DialogueEv (Ch s) (SFact s))
  | state (x : StEv s)
  deriving DecidableEq, Repr

inductive E (s : Spec) where
  | action (x : A s)
  | goal (x : GoalEv (Ch s) (SFact s) (A s))
  deriving DecidableEq, Repr

/-- The world is first-order data: what varies per character or object is a
table (by index) over a default, never a function. The kernel then evaluates a
state to a value instead of a growing chain of closures, so a state can be
written down, compared by `decide`, and used as a checkpoint. `W.loc`,
`W.beliefs`, ... read the tables with the same meaning the functions had. -/
structure W (s : Spec) where
  locT : List (Nat × Pl s)
  known : List (Ch s)
  holderT : List (Nat × Option (Ch s))
  objLocT : List (Nat × Pl s)
  objKnown : List (Ob s)
  beliefsT : List (Nat × List (Held (Ch s) (SFact s)))
  bondT : List ((Nat × Nat × Dim) × Nat)
  consent : List (Ch s × Ch s × Act) := []
  questions : List (Ch s × Ch s × SFact s) := []
  promises : List (Ch s × Ch s × (SFact s × Bool)) := []
  requests : List (Ch s × Ch s × (SFact s × Bool)) := []
  goalsT : List (Nat × List (SFact s × Bool))
  plansT : List (Nat × List (Plan (A s) (SFact s))) := []
  clock : Nat := 0
  /-- current values of the state atoms that have changed -/
  states : List (Nat × Bool) := []
  deriving DecidableEq, Repr

/-- A table's entry for `k`, or the default. -/
def tget {α β : Type} [BEq α] (t : List (α × β)) (k : α) (d : β) : β :=
  match t.find? (·.1 == k) with
  | some (_, v) => v
  | none => d

/-- Set a table's entry (one entry per key). -/
def tset {α β : Type} [BEq α] (t : List (α × β)) (k : α) (v : β) : List (α × β) :=
  (k, v) :: t.filter (·.1 != k)

/-- Characters whose place is not given are offstage (a place past the story's own). -/
def W.loc (w : W s) (c : Ch s) : Pl s := tget w.locT c.i ⟨s.places.length⟩
def W.holder (w : W s) (o : Ob s) : Option (Ch s) := tget w.holderT o.i none
def W.objLoc (w : W s) (o : Ob s) : Pl s := tget w.objLocT o.i ⟨0⟩
def W.beliefs (w : W s) (c : Ch s) : List (Held (Ch s) (SFact s)) := tget w.beliefsT c.i []
def W.bond (w : W s) (a b : Ch s) (k : Dim) : Nat := tget w.bondT (a.i, b.i, k) 0
def W.goals (w : W s) (c : Ch s) : List (SFact s × Bool) := tget w.goalsT c.i []
def W.plans (w : W s) (c : Ch s) : List (Plan (A s) (SFact s)) := tget w.plansT c.i []

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-! ## Facts -/

def Fact.supersedes (s : Spec) : Fact → Fact → Bool
  | .at_ c _, .at_ c' _ => c == c'
  | .objAt o _, .objAt o' _ | .objAt o _, .holds _ o' | .holds _ o, .holds _ o'
  | .holds _ o, .objAt o' _ => o == o'
  | .atom i, .atom j =>
    -- one lookup decides for the many atoms in no group (this runs inside every
    -- consistency check of every view)
    i != j && match s.atoms[i]? with
      | some a => a.group != "" && match s.atoms[j]? with
        | some b => a.group == b.group
        | none => false
      | none => false
  | _, _ => false

def Fact.fluent (s : Spec) : Fact → Bool
  | .at_ .. | .objAt .. | .holds .. => true
  | .atom i => (s.atoms[i]?.map (·.state)).getD false
  | _ => false

instance : Supersedes (SFact s) := ⟨fun a b => a.f.supersedes s b.f⟩
instance : Fluent (SFact s) := ⟨fun a => a.f.fluent s⟩
instance : Lore (SFact s) :=
  ⟨s.lore.map fun (body, (h, b)) => ⟨body.map fun (f, p) => (⟨f⟩, p), (⟨h⟩, b)⟩⟩

instance : Inject (SpaceFact (Ch s) (Pl s) (Ob s)) (SFact s) where
  inj | .at_ c p => ⟨.at_ c.i p.i⟩ | .objAt o p => ⟨.objAt o.i p.i⟩ | .holds c o => ⟨.holds c.i o.i⟩
instance : Inject (SocialFact (Ch s)) (SFact s) where
  inj | .did a b x => ⟨.did a.i b.i x⟩

/-! ## The world's lenses -/

instance : HasSpace (W s) (Ch s) (Pl s) (Ob s) where
  loc := W.loc
  setLoc w c p := { w with locT := tset w.locT c.i p }
  holder := W.holder
  setHolder w o h := { w with holderT := tset w.holderT o.i h }
  objLoc := W.objLoc
  setObjLoc w o p := { w with objLocT := tset w.objLocT o.i p }

instance : PartialLoc (W s) (Ch s) where
  locKnown w c := w.known.contains c
  assumeAt w a b := { w with locT := tset w.locT a.i (w.loc b), known := a :: w.known }
  markLoc w c := { w with known := c :: w.known }

instance : PartialObj (W s) (Ob s) where
  objKnown w o := w.objKnown.contains o
  markObj w o := { w with objKnown := o :: w.objKnown }

instance : HasMinds (W s) (Ch s) (SFact s) :=
  ⟨W.beliefs, fun w c bs => { w with beliefsT := tset w.beliefsT c.i bs }⟩

instance : HasBonds (W s) (Ch s) where
  bond := W.bond
  setBond w a b k n := { w with bondT := tset w.bondT (a.i, b.i, k) n }
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
  setGoals w c g := { w with goalsT := tset w.goalsT c.i g }
  plans := W.plans
  setPlans w c p := { w with plansT := tset w.plansT c.i p }

instance : Clock (W s) := ⟨W.clock, fun w => { w with clock := w.clock + 1 }⟩

def lookup {β : Type} (xs : List (Nat × β)) (k : Nat) : Option β :=
  (xs.find? (·.1 == k)).map (·.2)

def W.atomNow (w : W s) (i : Nat) : Bool :=
  (lookup w.states i).getD ((s.atoms[i]?.map (·.truth)).getD false)

/-- Where a spot is, when it is fixed: a place, or a fixture's place. -/
def Spec.spotPlace (s : Spec) : Spot → Option Nat
  | .place p => some p
  | .thing t => (s.things[t]?).bind (·.place)
  | .obj _ => none

def Fact.truth (w : W s) : Fact → Bool
  | .at_ c p => w.loc ⟨c⟩ == ⟨p⟩
  | .objAt o p => w.holder ⟨o⟩ == none && w.objLoc ⟨o⟩ == ⟨p⟩
  | .holds c o => w.holder ⟨o⟩ == some ⟨c⟩
  | .did _ _ _ => true
  | .atom i => w.atomNow i

instance : Truth (W s) (SFact s) := ⟨fun w f => f.f.truth w⟩
instance : Credence (W s) (Ch s) (SFact s) := socialCredence
instance : Rapport (W s) (Ch s) := bondRapport

/-! ## State changes -/

def Spec.isState (s : Spec) (a : Nat) : Bool := (s.atoms[a]?.map (·.state)).getD false

def Spec.stateLabel (s : Spec) (a : Nat) : String := (s.atoms[a]?.map (·.label)).getD s!"?{a}"

/-- Where a state's change must happen: the place of what it is about. -/
def Spec.stateWhere (s : Spec) (a : Nat) : Option Nat :=
  (s.atoms[a]?.bind (·.about)).bind s.spotPlace

def StEv.ok3 (w : W s) : StEv s → Tri
  | .make c a v =>
    if !s.isState a || w.atomNow a == v then .no
    else match s.stateWhere a with
      | some p => if w.known.contains c then Tri.ofBool (w.loc c == ⟨p⟩) else .unknown
      | none => .yes
  | .become a v => Tri.ofBool (s.isState a && w.atomNow a != v)

def StEv.why (w : W s) : StEv s → String
  | .make c a v =>
    if !s.isState a then s!"'{s.stateLabel a}' is not a state that can change (mark the atom \"state\": true)"
    else if w.atomNow a == v then s!"it is already so: {if v then "" else "not: "}{s.stateLabel a}"
    else if !w.known.contains c then "assumes they were where it is"
    else "they are not where it is"
  | .become a v =>
    if !s.isState a then s!"'{s.stateLabel a}' is not a state that can change (mark the atom \"state\": true)"
    else if w.atomNow a == v then s!"it is already so: {if v then "" else "not: "}{s.stateLabel a}"
    else ""

def StEv.step (w : W s) : StEv s → W s
  | .make c a v =>
    let w := match s.stateWhere a with
      | some p => if w.known.contains c then w else { w with locT := tset w.locT c.i ⟨p⟩, known := c :: w.known }
      | none => w
    { w with states := (a, v) :: w.states.filter (·.1 != a) }
  | .become a v => { w with states := (a, v) :: w.states.filter (·.1 != a) }

instance : Domain (W s) (StEv s) where
  ok w e := e.ok3 w == .yes
  ok3 w e := e.ok3 w
  why w e := e.why w
  step w e := e.step w

/-! ## Events: injections and dispatch -/

instance : Inject (SpaceEv (Ch s) (Pl s) (Ob s)) (A s) := ⟨.space⟩
instance : Inject (MindEv (Ch s) (SFact s)) (A s) := ⟨.mind⟩
instance : Inject (SocialEv (Ch s)) (A s) := ⟨.social⟩
instance : Inject (DialogueEv (Ch s) (SFact s)) (A s) := ⟨.dialogue⟩
instance : Inject (A s) (E s) := ⟨.action⟩
instance : Inject (GoalEv (Ch s) (SFact s) (A s)) (E s) := ⟨.goal⟩

instance : Domain (W s) (A s) where
  ok w | .space x => Domain.ok w x | .mind x => Domain.ok w x
       | .social x => Domain.ok w x | .dialogue x => Domain.ok w x | .state x => Domain.ok w x
  ok3 w | .space x => Domain.ok3 w x | .mind x => Domain.ok3 w x
        | .social x => Domain.ok3 w x | .dialogue x => Domain.ok3 w x | .state x => Domain.ok3 w x
  why w | .space x => Domain.why w x | .mind x => Domain.why w x
        | .social x => Domain.why w x | .dialogue x => Domain.why w x | .state x => Domain.why w x
  step w | .space x => Domain.step w x | .mind x => Domain.step w x
         | .social x => Domain.step w x | .dialogue x => Domain.step w x | .state x => Domain.step w x

instance : Domain (W s) (E s) where
  ok w | .action x => Domain.ok w x | .goal x => Domain.ok w x
  ok3 w | .action x => Domain.ok3 w x | .goal x => Domain.ok3 w x
  why w | .action x => Domain.why w x | .goal x => Domain.why w x
  step w | .action x => Domain.step w x | .goal x => Domain.step w x

instance : Observable (W s) (A s) (SFact s) (Pl s) where
  seen w | .space x => Observable.seen w x | .social x => Observable.seen w x
         -- whoever is there sees a state come about (a negative one shows nothing to see)
         | .state (.make c a true) => some (w.loc c, [⟨.atom a⟩])
         | .state (.become a true) => (s.stateWhere a).map fun p => (⟨p⟩, [⟨.atom a⟩])
         | _ => none

instance : Observable (W s) (E s) (SFact s) (Pl s) where
  seen w | .action x => Observable.seen w x | .goal _ => none

/-- Who must have a reason: movers, takers and givers, and whoever initiates an
intimate act. Talk (flirting, confiding, asking, agreeing) is expressive and
needs no goal. -/
instance : Purpose (W s) (A s) (Ch s) (SFact s) where
  agent | .space x => Purpose.agent (W := W s) (Φ := SFact s) x
        | .social (.act a _ _) => some a
        | .state (.make c _ _) => some c
        | _ => none
  effects w | .space x => Purpose.effects (C := Ch s) w x
            | .social x => Purpose.effects (C := Ch s) w x
            | .state (.make _ a v) => [(⟨.atom a⟩, v)]
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
  | .make c a v => some (.state (.make ⟨c⟩ a v))
  | .become a v => some (.state (.become a v))
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

/-- The opening state. -/
def Spec.start (s : Spec) : W s where
  -- characters whose place the text has not given are offstage (a place past
  -- the story's own), so they witness and overhear nothing until they appear
  locT := s.startAt.map fun (c, p) => (c, ⟨p⟩)
  known := s.startAt.map (⟨·.1⟩)
  holderT := s.startHeld.map fun (o, c) => (o, some ⟨c⟩)
  objLocT := s.startObjAt.map fun (o, p) => (o, ⟨p⟩)
  objKnown := (s.startObjAt ++ s.startHeld).map (⟨·.1⟩)
  beliefsT := (List.range s.chars.length).filterMap fun c =>
    match (s.knows.filter (·.1 == c)).map fun (_, l) => own l with
    | [] => none
    | bs => some (c, bs)
  bondT := s.bonds.map fun (x, y, j, n) => ((x, y, j), n)
  goalsT := (List.range s.chars.length).filterMap fun c =>
    match (s.goals.filter (·.1 == c)).map fun (_, g) => lit g with
    | [] => none
    | gs => some (c, gs)

end LangLib.Studio
