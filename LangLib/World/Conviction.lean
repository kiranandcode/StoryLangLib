import LangLib.World.Domain

/-!
# Convictions: a belief held against the evidence, until the evidence is enough

`Mind` revises a belief as soon as one piece of evidence is strong enough. Some
beliefs do not work like that. Someone sure that nobody could be interested in
her registers each sign that someone is (he remembered her order, he walked her
to the train, he said so) and explains each one away (he is like this with
everyone; he wants a co-author); only when the signs pile up past what her
explanations can cover does she concede.

`ConvictionSight.holdout c x = some n` says `c` holds out against `x` until
`n` signs of it have been registered. Events:

* `datum c x`: `c` registers a sign of `x` (always allowed: signs happen);
* `dismiss c x`: `c` explains a sign away; there must be a sign not yet
  explained, and she has not conceded;
* `concede c x`: `c` comes to accept `x`, allowed only once `n` signs are in.

Nobody holds out by default, and then conceding is always allowed
(`concede_free`). The gate is a theorem (`concede_needs_data`): an early
concession is out of character, and the checker says how many signs are still
missing.
-/

namespace LangLib.World

/-- Which propositions a character holds out against, and for how many signs. -/
class ConvictionSight (C X : Type) where
  holdout : C → X → Option Nat := fun _ _ => none

instance (priority := low) {C X : Type} : ConvictionSight C X := {}

class HasConvictions (W : Type) (C X : outParam Type) where
  /-- `(c, x, n)`: `c` has registered `n` signs of `x` -/
  data : W → List (C × X × Nat)
  setData : W → List (C × X × Nat) → W
  /-- `(c, x, n)`: `c` has explained `n` of them away -/
  dismissed : W → List (C × X × Nat)
  setDismissed : W → List (C × X × Nat) → W
  /-- `(c, x)`: `c` has conceded `x` -/
  conceded : W → List (C × X)
  setConceded : W → List (C × X) → W

inductive ConvEv (C X : Type) where
  | datum (c : C) (x : X)
  | dismiss (c : C) (x : X)
  | concede (c : C) (x : X)
  deriving DecidableEq, Repr

variable {W C X : Type} [DecidableEq C] [DecidableEq X] [HasConvictions W C X] [ConvictionSight C X]

open HasConvictions

def countOf (l : List (C × X × Nat)) (c : C) (x : X) : Nat :=
  ((l.find? fun (c', x', _) => c' == c && x' == x).map (·.2.2)).getD 0

def bumpCount (l : List (C × X × Nat)) (c : C) (x : X) : List (C × X × Nat) :=
  (c, x, countOf l c x + 1) :: l.filter fun (c', x', _) => !(c' == c && x' == x)

def hasConceded (w : W) (c : C) (x : X) : Bool := (conceded w).contains (c, x)

def ConvEv.ok (w : W) : ConvEv C X → Bool
  | .datum _ _ => true
  | .dismiss c x => !hasConceded w c x && countOf (dismissed w) c x < countOf (data w) c x
  | .concede c x => !hasConceded w c x &&
    match ConvictionSight.holdout c x with
    | some n => countOf (data w) c x ≥ n
    | none => true

def ConvEv.step (w : W) : ConvEv C X → W
  | .datum c x => setData w (bumpCount (data w) c x)
  | .dismiss c x => setDismissed w (bumpCount (dismissed w) c x)
  | .concede c x => setConceded w ((c, x) :: conceded w)

instance : Domain W (ConvEv C X) where
  ok := ConvEv.ok
  step := ConvEv.step
  why w
    | .datum _ _ => ""
    | .dismiss c x => if hasConceded w c x then "they already accept it; there is nothing left to explain away"
        else "there is no sign of it left to explain away"
    | .concede c x =>
      if hasConceded w c x then "they already accept it" else
      match ConvictionSight.holdout c x with
      | some n => s!"out of character: they hold out against this until the signs outrun their explanations; " ++
          s!"to justify it, first establish: more signs of it ({countOf (data w) c x} of {n} registered)"
      | none => ""

/-- An early concession is ruled out: fewer signs than the holdout. -/
theorem concede_needs_data (w : W) (c : C) (x : X) (n : Nat)
    (h : ConvictionSight.holdout c x = some n) (hn : countOf (data w) c x < n) :
    ConvEv.ok w (.concede c x) = false := by
  simp [ConvEv.ok, h]; omega

/-- Without a holdout, a concession (not yet made) is always allowed. -/
theorem concede_free (w : W) (c : C) (x : X)
    (h : ConvictionSight.holdout c x = none) (hc : hasConceded w c x = false) :
    ConvEv.ok w (.concede c x) = true := by
  simp [ConvEv.ok, h, hc]

omit [HasConvictions W C X] [ConvictionSight C X] in
/-- Each sign brings the concession one step nearer. -/
theorem bump_counts (l : List (C × X × Nat)) (c : C) (x : X) :
    countOf (bumpCount l c x) c x = countOf l c x + 1 := by
  simp [bumpCount, countOf]

end LangLib.World
