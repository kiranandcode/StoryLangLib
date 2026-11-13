import LangLib.Studio.World

/-!
# Refinement between layers of a story

Top-down writing goes beats → paragraph plans → prose. Each layer is a story
over its own vocabulary, and each finer layer must *refine* the coarser one:
abstracted to the coarser vocabulary, the finer story is the coarser story.

* `Refines abs fine coarse := fine.filterMap abs = coarse`: events that
  abstract to `none` are detail the coarser layer does not mention.
* `Refines.trans`: refinement composes, so prose that refines its plans, whose
  plans refine the beats, refines the beats.
* `RefinesValid`: refinement plus validity of both layers, each in its own
  world; for a concrete story it is decidable.

## The beat layer

A beat is a coarse event with STRIPS-style preconditions and effects over
named story conditions ("the note is misread", "she knows the truth"). A beat
story is valid when each beat's preconditions hold when it happens, which
catches a resolution before its complication or a kiss before the
negotiation. A beat may name *key* fine events: the fine event that is that
beat (Mara noticing the note *is* the misreading). `Beats.abs` maps a key
event to its beat and everything else to `none`.
-/

namespace LangLib.Studio
open LangLib.World

def Refines {F C : Type} (abs : F → Option C) (fine : List F) (coarse : List C) : Prop :=
  fine.filterMap abs = coarse

instance {F C : Type} [DecidableEq C] (abs : F → Option C) (fine : List F) (coarse : List C) :
    Decidable (Refines abs fine coarse) := inferInstanceAs (Decidable (_ = _))

theorem Refines.refl {F : Type} (xs : List F) : Refines some xs xs := by
  simp [Refines]

theorem Refines.trans {F M C : Type} {f : F → Option M} {g : M → Option C}
    {xs : List F} {ys : List M} {zs : List C}
    (h₁ : Refines f xs ys) (h₂ : Refines g ys zs) : Refines (fun x => (f x).bind g) xs zs := by
  unfold Refines at *
  subst h₁ h₂
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [hx, ih]
    | some m => cases hm : g m <;> simp [hx, hm, ih]

/-- Refinement is preserved by concatenation: paragraph by paragraph is enough. -/
theorem Refines.append {F C : Type} {abs : F → Option C} {a b : List F} {c d : List C}
    (h₁ : Refines abs a c) (h₂ : Refines abs b d) : Refines abs (a ++ b) (c ++ d) := by
  unfold Refines at *; simp [List.filterMap_append, h₁, h₂]

theorem Refines.flatten {F C : Type} {abs : F → Option C} :
    ∀ {xs : List (List F)} {ys : List (List C)}, xs.length = ys.length →
    (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), Refines abs xs[i] ys[i]) →
    Refines abs xs.flatten ys.flatten
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.flatten_cons]
    exact Refines.append (h 0 (by simp) (by simp))
      (Refines.flatten (by simpa using hl) fun i h₁ h₂ =>
        h (i + 1) (by simpa using h₁) (by simpa using h₂))

/-! ## Beats -/

structure Beat where
  id : String
  label : String := ""
  /-- conditions (by index) that must hold -/
  pre : List Nat := []
  add : List Nat := []
  del : List Nat := []
  /-- the fine events that are this beat -/
  keys : List Ev := []
  deriving Repr, DecidableEq

structure Beats where
  conds : List String
  vocab : List Beat
  /-- conditions holding at the start -/
  init : List Nat := []
  deriving Repr, DecidableEq

/-- The beat world: which conditions hold. -/
structure BeatW where
  holds : List Nat
  deriving DecidableEq, Repr

/-- A beat, by index into the vocabulary of `B`. -/
structure BeatEv (B : Beats) where
  i : Nat
  deriving DecidableEq, Repr

def Beats.beat (B : Beats) (i : Nat) : Beat := B.vocab.getD i {id := "?"}

instance {B : Beats} : Domain BeatW (BeatEv B) where
  ok w b := (B.beat b.i).pre.all w.holds.contains
  step w b := ⟨((w.holds.filter fun c => !(B.beat b.i).del.contains c) ++ (B.beat b.i).add).eraseDups⟩
  why w b :=
    let missing := (B.beat b.i).pre.filter fun c => !w.holds.contains c
    s!"beat \"{(B.beat b.i).id}\" needs first: " ++ ", ".intercalate (missing.map (B.conds.getD · "?"))

instance {B : Beats} : Perceive BeatW (BeatEv B) := Perceive.none

def Beats.start (B : Beats) : BeatW := ⟨B.init⟩

/-- A fine event's beat, if it is the key event of one. -/
def Beats.abs (B : Beats) (e : Ev) : Option (BeatEv B) :=
  (B.vocab.findIdx? fun b => b.keys.contains e).map (⟨·⟩)

/-- Refinement plus validity of both layers. -/
def RefinesValid (s : Spec) (B : Beats) (fine : List Ev) (coarse : List (BeatEv B)) : Prop :=
  Refines B.abs fine coarse ∧ Valid B.start coarse ∧ Plausible s.start (fine.map (Ev.toE s))

instance (s : Spec) (B : Beats) (fine : List Ev) (coarse : List (BeatEv B)) :
    Decidable (RefinesValid s B fine coarse) := by unfold RefinesValid; infer_instance

end LangLib.Studio

namespace LangLib.Studio
open LangLib.World

/-! ## Story time, paragraph by paragraph -/

variable {W E : Type} [Domain W E] [Perceive W E] [Invariant W] [Clock W]

/-- Indices of the events that go through only by assumption. -/
def assumedAt : W → List E → Nat → List Nat
  | _, [], _ => []
  | w, e :: es, i =>
    (if Domain.ok3 w e == .unknown then [i] else []) ++ assumedAt (next w e) es (i + 1)

/-- The events told in paragraphs `0 … k`, in story-time order (`owner[i]` is
the paragraph that tells event `i`). -/
def _root_.LangLib.World.Timed.upTo (t : Timed E) (owner : List Nat) (k : Nat) : List E :=
  (t.timeline.byEffect.filter fun i => owner.getD i 0 ≤ k).filterMap (t.told[·]?)

/-- The timeline fits the text, and in story-time order nothing is ruled out. -/
def _root_.LangLib.World.Timed.Plausible (w : W) (s : Timed E) : Prop :=
  s.timeline.length = s.told.length ∧ s.timeline.Satisfies s.constraints ∧
  s.metric.all (·.sat s.timeline) = true ∧ World.Plausible w s.chrono

instance (w : W) (s : Timed E) : Decidable (s.Plausible w) := by
  unfold Timed.Plausible; infer_instance

end LangLib.Studio
