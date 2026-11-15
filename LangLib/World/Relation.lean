import LangLib.World.Domain

/-!
# Typed relations with declared laws

Social's bonds are four fixed dimensions. Stories need more kinds of tie, and
the kinds differ by story: friends, roommates, family, a gang, "threatens",
"protects", "trusts". Here a story declares its relation types `R` and their
laws (`RelLaws`), and relation facts are graded: `rel w r a b` is a level,
`0` meaning absent.

Laws:
* `symmetric r`: setting `r a b` sets `r b a` (friends, roommates);
* `excludes r r'`: holding `r a b` ends `r' a b` (and `r' b a` when `r'` is
  symmetric): "threatens" ends "friends";
* `requires r = some (r', k)`: `r a b` can only be set while `r' a b ≥ k`
  (disclosing needs trust; "partners" might need "dating").

Events: `relate a r b` (set to at least 1), `raise a r b` (one level up),
`lower a r b`, `unrelate a r b` (to 0). Every event is decidable, so a story's
web of ties is checked like its places.
-/

namespace LangLib.World

class RelLaws (R : Type) where
  symmetric : R → Bool := fun _ => false
  excludes : R → List R := fun _ => []
  requires : R → Option (R × Nat) := fun _ => none

class HasRels (W : Type) (C R : outParam Type) where
  rel : W → R → C → C → Nat
  setRel : W → R → C → C → Nat → W

inductive RelEv (C R : Type) where
  | relate (a : C) (r : R) (b : C)
  | raise (a : C) (r : R) (b : C)
  | lower (a : C) (r : R) (b : C)
  | unrelate (a : C) (r : R) (b : C)
  deriving DecidableEq, Repr

variable {W C R : Type} [DecidableEq C] [DecidableEq R] [HasRels W C R] [RelLaws R]

open HasRels

/-- Set `r a b` to `n`, with the laws: the mirror for a symmetric type, and
every excluded type between the pair ended. -/
def setRelLaw (w : W) (r : R) (a b : C) (n : Nat) : W :=
  let w := setRel w r a b n
  let w := if RelLaws.symmetric r then setRel w r b a n else w
  if n == 0 then w else
  (RelLaws.excludes r).foldl (fun w r' =>
    let w := setRel w r' a b 0
    if RelLaws.symmetric r' then setRel w r' b a 0 else w) w

def relReady (w : W) (r : R) (a b : C) : Bool :=
  match RelLaws.requires r with
  | some (r', k) => rel w r' a b ≥ k
  | none => true

def RelEv.ok (w : W) : RelEv C R → Bool
  | .relate a r b | .raise a r b => a != b && relReady w r a b
  | .lower a r b | .unrelate a r b => rel w r a b > 0

def RelEv.step (w : W) : RelEv C R → W
  | .relate a r b => setRelLaw w r a b (max 1 (rel w r a b))
  | .raise a r b => setRelLaw w r a b (rel w r a b + 1)
  | .lower a r b => setRelLaw w r a b (rel w r a b - 1)
  | .unrelate a r b => setRelLaw w r a b 0

instance : Domain W (RelEv C R) where
  ok := RelEv.ok
  step := RelEv.step
  why w
    | .relate a r b | .raise a r b =>
      if a == b then "a tie needs two people" else
      match RelLaws.requires r with
      | some (r', k) => s!"this tie needs another first, at level {k} (has {rel w r' a b})"
      | none => ""
    | .lower _ _ _ | .unrelate _ _ _ => "there is no such tie to weaken"

end LangLib.World
