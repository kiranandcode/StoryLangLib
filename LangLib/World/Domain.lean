import LangLib.World.Time

/-!
# Domains: composable story-world semantics

A story world is a state `W` and an event type `E`. A *module* (space, minds,
relationships, a magic system, ...) contributes events with a `Domain`
instance: when an event is allowed (`ok`), what it changes (`step`), and why it
is not allowed (`why`). Modules ask for the parts of the state they need
through small lens classes (`HasLoc`, `HasMinds`, ...), so one story's state
can serve many modules.

* Event types compose by `⊕`: `Domain W (E₁ ⊕ E₂)` from the two parts, and
  `Inject` puts a module's event into the story's sum (`ev e`).
* `Perceive` runs after every step, so a minds module can let witnesses learn
  what other modules' events made visible; without one it does nothing.
* `Valid w es`: every event is allowed in the state the previous ones made;
  decidable, so validity of a concrete story is proved by `decide`.
* `Story`: events in the order the text tells them, with interval constraints;
  `Timed` adds a timeline (the consistency certificate), and validity is
  checked in chronological order (by end point: an event takes effect when it
  ends).
-/

namespace LangLib.World

class Domain (W : Type) (E : Type) where
  ok : W → E → Bool
  step : W → E → W
  why : W → E → String := fun _ _ => "not allowed"

instance {W E₁ E₂ : Type} [Domain W E₁] [Domain W E₂] : Domain W (E₁ ⊕ E₂) where
  ok w | .inl e => Domain.ok w e | .inr e => Domain.ok w e
  step w | .inl e => Domain.step w e | .inr e => Domain.step w e
  why w | .inl e => Domain.why w e | .inr e => Domain.why w e

/-- `E` is one of the summands of `S`. -/
class Inject (E S : Type) where
  inj : E → S

instance {E : Type} : Inject E E := ⟨id⟩
instance {E S₁ S₂ : Type} [Inject E S₁] : Inject E (S₁ ⊕ S₂) := ⟨fun e => .inl (Inject.inj e)⟩
instance (priority := low) {E S₁ S₂ : Type} [Inject E S₂] : Inject E (S₁ ⊕ S₂) :=
  ⟨fun e => .inr (Inject.inj e)⟩

/-- Put a module's event (or fact) into the story's sum type. -/
abbrev ev {E S : Type} [Inject E S] (e : E) : S := Inject.inj e

/-- Runs after each step: `perceive before e after`. -/
class Perceive (W E : Type) where
  perceive : W → E → W → W

instance (priority := low) {W E : Type} : Perceive W E := ⟨fun _ _ w => w⟩

/-- Story time, advanced by one after every event. Without an instance it
stands still at 0. -/
class Clock (W : Type) where
  now : W → Nat
  tick : W → W

instance (priority := low) {W : Type} : Clock W := ⟨fun _ => 0, id⟩

/-- A property every state of a story must keep (e.g. every mind consistent).
Without an instance it is always true. -/
class Invariant (W : Type) where
  holds : W → Bool

instance (priority := low) {W : Type} : Invariant W := ⟨fun _ => true⟩

variable {W E : Type} [Domain W E] [Perceive W E] [Invariant W] [Clock W]

def next (w : W) (e : E) : W := Clock.tick (Perceive.perceive w e (Domain.step w e))

def run (w : W) : List E → W
  | [] => w
  | e :: es => run (next w e) es

inductive Valid : W → List E → Prop
  | nil {w} : Valid w []
  | cons {w e es} : Domain.ok w e = true → Invariant.holds (next w e) = true →
      Valid (next w e) es → Valid w (e :: es)

/-- `w ⊨ es`: the events `es` make a valid story from state `w`. -/
notation:50 w " ⊨ " es => Valid w es

def validB : W → List E → Bool
  | _, [] => true
  | w, e :: es => Domain.ok w e && Invariant.holds (next w e) && validB (next w e) es

theorem validB_iff : ∀ (w : W) (es : List E), validB w es = true ↔ Valid w es
  | _, [] => by simp [validB]; exact .nil
  | w, e :: es => by
    simp only [validB, Bool.and_eq_true, validB_iff _ es]
    exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ => .cons h₁ h₂ h₃, fun | .cons h₁ h₂ h₃ => ⟨⟨h₁, h₂⟩, h₃⟩⟩

instance (w : W) (es : List E) : Decidable (Valid w es) :=
  decidable_of_iff _ (validB_iff w es)

/-- The first event that is not allowed, with its position and reason. -/
def firstFailure : W → List E → Nat → Option (Nat × String)
  | _, [], _ => none
  | w, e :: es, i =>
    if !Domain.ok w e then some (i, Domain.why w e)
    else if !Invariant.holds (next w e) then some (i, "it would leave the story inconsistent")
    else firstFailure (next w e) es (i + 1)

/-! ## Time over a plain sequence -/

/-- The state after the first `n` events. -/
def atStep (w : W) (es : List E) (n : Nat) : W := run w (es.take n)

def Was (w : W) (es : List E) (p : W → Bool) : Bool :=
  (List.range (es.length + 1)).any fun n => p (atStep w es n)

def Throughout (w : W) (es : List E) (p : W → Bool) : Bool :=
  (List.range (es.length + 1)).all fun n => p (atStep w es n)

/-! ## Stories told out of order -/

structure Story (E : Type) where
  /-- events in the order the text tells them; event `i` is `told[i]` -/
  told : List E
  /-- what the text says about when -/
  constraints : List Constraint := []
  /-- what the text says about how long -/
  metric : List Metric := []

/-- A story with an endpoint assignment for its events. -/
structure Timed (E : Type) extends Story E where
  timeline : Timeline

/-- Insertion sort (structural, so it reduces in kernel proofs). -/
def insertBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

def sortBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy le x (sortBy le xs)

/-- Event indices in order of effect: by end point, then start, then index. -/
def Timeline.byEffect (t : Timeline) : List Nat :=
  (sortBy (fun (i, a) (j, b) =>
    a.e < b.e || (a.e == b.e && (a.s < b.s || (a.s == b.s && i ≤ j))))
    ((List.range t.length).zip t)).map (·.1)

def Timed.chrono (s : Timed E) : List E := s.timeline.byEffect.filterMap (s.told[·]?)

/-- The timeline fits the text's constraints, and the events are valid in
chronological order. -/
def Timed.Valid (w : W) (s : Timed E) : Prop :=
  s.timeline.length = s.told.length ∧ s.timeline.Satisfies s.constraints ∧
  s.metric.all (·.sat s.timeline) = true ∧ World.Valid w s.chrono

instance (w : W) (s : Timed E) : Decidable (s.Valid w) := by
  unfold Timed.Valid; infer_instance

/-- A timeline found by the solver (untrusted; `Timed.Valid` re-checks it). -/
def Story.solved (s : Story E) : Option (Timed E) :=
  (solve s.told.length s.constraints s.metric).map fun t => { s with timeline := t }

/-- The state at story time `τ`: every event that ended by `τ` has taken effect. -/
def Timed.stateAt (w : W) (s : Timed E) (τ : Nat) : W :=
  run w (s.timeline.byEffect.filterMap fun i =>
    match s.timeline[i]?, s.told[i]? with
    | some iv, some e => if iv.e ≤ τ then some e else none
    | _, _ => none)

/-- `p` holds at every time point inside event `i`'s interval. The state only
changes when an event ends, so it suffices to check the interval's start and
every event end inside it. -/
def Timed.during (w : W) (s : Timed E) (i : Nat) (p : W → Bool) : Bool :=
  match s.timeline[i]? with
  | some iv =>
    (iv.s :: (s.timeline.map (·.e)).filter (fun τ => iv.s < τ && τ < iv.e)).all
      fun τ => p (s.stateAt w τ)
  | none => false

end LangLib.World
