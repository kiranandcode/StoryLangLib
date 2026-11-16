import LangLib.World.Domain

/-!
# Ties: typed relations with declared laws

Social's bonds are four fixed dimensions. Stories need more kinds of tie, and
the kinds differ by story: friends, roommates, family, a gang, "threatens",
"protects", "trusts". Here a story declares its relation types `R` and their
laws (`TieLaws`), and relation facts are graded: `tie w r a b` is a level,
`0` meaning absent.

Laws:
* `symmetric r`: setting `r a b` sets `r b a` (friends, roommates);
* `excludes r r'`: holding `r a b` ends `r' a b` (and `r' b a` when `r'` is
  symmetric): "threatens" ends "friends";
* `requires r = some (r', k)`: `r a b` can only be set while `r' a b ≥ k`
  (disclosing needs trust; "partners" might need "dating");
* `forbids r = some (r', k)`: `r a b` can only be set while `r' a b < k` and
  `r' b a < k`: a reason not to act is a gate too (no romance while one of them
  convenes the other's group) (`forbids_no_start`).

Events: `relate a r b` (set to at least 1), `raise a r b` (one level up),
`lower a r b`, `unrelate a r b` (to 0). Every event is decidable, so a story's
web of ties is checked like its places.

Personas can also bound ties: `TieSight.aloof a r` says `a` never starts a tie
of type `r`; they can only answer one held toward them (`r b a > 0`). Someone
who makes no friends can still return a friendship kept for them
(`aloof_no_start`, `aloof_answers`). Nobody is aloof by default.
-/

namespace LangLib.World

class TieLaws (R : Type) where
  symmetric : R → Bool := fun _ => false
  excludes : R → List R := fun _ => []
  requires : R → Option (R × Nat) := fun _ => none
  forbids : R → Option (R × Nat) := fun _ => none

/-- Tie types a character never starts, only answers. -/
class TieSight (C R : Type) where
  aloof : C → R → Bool := fun _ _ => false

instance (priority := low) {C R : Type} : TieSight C R := {}

class HasTies (W : Type) (C R : outParam Type) where
  tie : W → R → C → C → Nat
  setTie : W → R → C → C → Nat → W

inductive TieEv (C R : Type) where
  | relate (a : C) (r : R) (b : C)
  | raise (a : C) (r : R) (b : C)
  | lower (a : C) (r : R) (b : C)
  | unrelate (a : C) (r : R) (b : C)
  deriving DecidableEq, Repr

variable {W C R : Type} [DecidableEq C] [DecidableEq R] [HasTies W C R] [TieLaws R] [TieSight C R]

open HasTies

/-- Set `r a b` to `n`, with the laws: the mirror for a symmetric type, and
every excluded type between the pair ended. -/
def setTieLaw (w : W) (r : R) (a b : C) (n : Nat) : W :=
  let w := setTie w r a b n
  let w := if TieLaws.symmetric r then setTie w r b a n else w
  if n == 0 then w else
  (TieLaws.excludes r).foldl (fun w r' =>
    let w := setTie w r' a b 0
    if TieLaws.symmetric r' then setTie w r' b a 0 else w) w

def tieReady (w : W) (r : R) (a b : C) : Bool :=
  (match TieLaws.requires r with
  | some (r', k) => tie w r' a b ≥ k
  | none => true) &&
  (match TieLaws.forbids r with
  | some (r', k) => tie w r' a b < k && tie w r' b a < k
  | none => true)

/-- `a` may start (or raise) `r` toward `b`: not aloof in `r`, or `b` holds `r` toward `a`. -/
def tieReach (w : W) (r : R) (a b : C) : Bool := !TieSight.aloof a r || tie w r b a > 0

def TieEv.ok (w : W) : TieEv C R → Bool
  | .relate a r b | .raise a r b => a != b && tieReady w r a b && tieReach w r a b
  | .lower a r b | .unrelate a r b => tie w r a b > 0

def TieEv.step (w : W) : TieEv C R → W
  | .relate a r b => setTieLaw w r a b (max 1 (tie w r a b))
  | .raise a r b => setTieLaw w r a b (tie w r a b + 1)
  | .lower a r b => setTieLaw w r a b (tie w r a b - 1)
  | .unrelate a r b => setTieLaw w r a b 0

instance : Domain W (TieEv C R) where
  ok := TieEv.ok
  step := TieEv.step
  why w
    | .relate a r b | .raise a r b =>
      if a == b then "a tie needs two people" else
      if !tieReach w r a b then "out of character: they never start this kind of tie, only answer one; " ++
        "to justify it, first establish: the other holds it toward them" else
      match TieLaws.forbids r with
      | some (r', k) =>
        if tie w r' a b ≥ k || tie w r' b a ≥ k then
          "out of character: another tie between them rules this one out for now; to justify it, first " ++
          "establish: that tie ended"
        else match TieLaws.requires r with
          | some (r', k) => s!"this tie needs another first, at level {k} (has {tie w r' a b})"
          | none => ""
      | none => match TieLaws.requires r with
        | some (r', k) => s!"this tie needs another first, at level {k} (has {tie w r' a b})"
        | none => ""
    | .lower _ _ _ | .unrelate _ _ _ => "there is no such tie to weaken"

/-- An aloof character cannot start the tie. -/
theorem aloof_no_start (w : W) (a b : C) (r : R) (h : TieSight.aloof a r = true) (h0 : tie w r b a = 0) :
    TieEv.ok w (.relate a r b) = false := by
  simp [TieEv.ok, tieReach, h, h0]

/-- But answering a tie held toward them is open to them (given the type's other laws). -/
theorem aloof_answers (w : W) (a b : C) (r : R) (hab : a ≠ b) (hr : tieReady w r a b = true) (h : tie w r b a > 0) :
    TieEv.ok w (.relate a r b) = true := by
  simp [TieEv.ok, tieReach, hab, hr, h]

/-- While the forbidding tie holds (either way), the tie cannot start. -/
theorem forbids_no_start (w : W) (a b : C) (r r' : R) (k : Nat) (h : TieLaws.forbids r = some (r', k))
    (hk : tie w r' a b ≥ k ∨ tie w r' b a ≥ k) : TieEv.ok w (.relate a r b) = false := by
  simp only [TieEv.ok, tieReady, h]
  rcases hk with hk | hk <;> simp [Nat.not_lt.mpr hk]

end LangLib.World
