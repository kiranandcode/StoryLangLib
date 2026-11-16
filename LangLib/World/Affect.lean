import LangLib.World.Care

/-!
# Affect: what characters feel, appraised from what happens to them

Prose says how characters feel all the time ("frightened", "teary",
"relieved", "embarrassed"), and the Studio could only mark such words as
impressions, unchecked. Here feelings are state: each character has a level of
each emotion `E` the story declares, and the level changes in two ways:

* **appraisal**: story-declared rules turn the events of other modules into
  feelings: being harmed (`Care.harm`) brings distress, being threatened
  (`Ties.relate _ threatens c`) brings fear, being tended (`Care.tend`, of a
  given need or any) or shielded calms it;
* **explicit** events, for what no rule appraises: `feel c e` (a feeling the
  text shows arising: embarrassment at a slip of the tongue), `calm c e`.

A word naming a feeling, said of a character, must then be backed by the state
(`Studio/Ext` holds the prose to it), so "a frightened thing" is checked, not
excused.

## Reading a feeling

Most people take a feeling as itself. Some first take certain feelings as an
**anomaly**: a datum to explain, not a want. `AffectReading.anomaly c e = some
n` says `c` takes `e` so, and needs `n` examinations (hypotheses tried and
failed) before it reads as itself. `examine c e` records one (the feeling must
be there to examine); `recognise c e` lets it read as itself, allowed only after
enough examinations; `own c e` is saying or acting on the feeling as a want
("I want you"), allowed only once it reads as itself. Until then a word naming
the feeling as itself is not backed either (`readAs`).

A feeling can also be the felt sign of a need (`AffectReading.signals e = some
k`: loneliness is the need for company, felt). Feeling it needs the need felt
(`Care.felt c c k`), so a character blind to a need of their own never feels
its sign, even after being told they have the need (`feel_sign_blind`).
-/

namespace LangLib.World

/-- What an event of another module makes its target feel (`d` levels up, or
down when negative). `none` for a need means any. -/
inductive AffectRule (K R E : Type) where
  | onHarm (k : Option K) (e : E) (d : Int)
  | onTend (k : Option K) (e : E) (d : Int)
  | onShield (e : E) (d : Int)
  | onTie (r : R) (e : E) (d : Int)
  deriving DecidableEq, Repr

class HasAffect (W : Type) (C E : outParam Type) where
  feels : W → C → E → Nat
  setFeels : W → C → E → Nat → W
  /-- `(c, e, n)`: `c` has examined the anomaly `e` `n` times -/
  examined : W → List (C × E × Nat) := fun _ => []
  setExamined : W → List (C × E × Nat) → W := fun w _ => w
  /-- `(c, e)`: `c` now reads `e` as itself -/
  recognised : W → List (C × E) := fun _ => []
  setRecognised : W → List (C × E) → W := fun w _ => w

/-- How a character takes a feeling: as an anomaly to examine first (`some n`:
after `n` examinations it reads as itself), and which need a feeling signals. -/
class AffectReading (C E : Type) (K : outParam Type) where
  anomaly : C → E → Option Nat := fun _ _ => none
  signals : E → Option K := fun _ => none

inductive AffEv (C E : Type) where
  | feel (c : C) (e : E)
  | calm (c : C) (e : E)
  deriving DecidableEq, Repr

variable {W C K R E : Type} [DecidableEq C] [DecidableEq K] [DecidableEq R] [DecidableEq E]
  [HasAffect W C E]

open HasAffect

def shiftFeel (w : W) (c : C) (e : E) (d : Int) : W :=
  setFeels w c e (Int.toNat (feels w c e + d))

/-- The feelings an event of `Care` or `Ties` brings about, by the rules. -/
def appraise (rules : List (AffectRule K R E)) : CareEv C K ⊕ TieEv C R → List (C × E × Int)
  | .inl (.harm _ c k) => rules.filterMap fun
    | .onHarm k' e d => if k'.all (· == k) then some (c, e, d) else none | _ => none
  | .inl (.tend _ c k) => rules.filterMap fun
    | .onTend k' e d => if k'.all (· == k) then some (c, e, d) else none | _ => none
  | .inl (.shield _ c _) => rules.filterMap fun
    | .onShield e d => some (c, e, d) | _ => none
  | .inr (.relate _ r c) | .inr (.raise _ r c) => rules.filterMap fun
    | .onTie r' e d => if r' == r then some (c, e, d) else none | _ => none
  | _ => []

def applyAffect (w : W) (ds : List (C × E × Int)) : W :=
  ds.foldl (fun w (c, e, d) => shiftFeel w c e d) w

instance : Domain W (AffEv C E) where
  ok w | .feel _ _ => true | .calm c e => feels w c e > 0
  step w | .feel c e => shiftFeel w c e 1 | .calm c e => shiftFeel w c e (-1)
  why _ | .feel _ _ => "" | .calm _ _ => "they do not feel that (any more)"

/-! ## Reading a feeling: anomalies and signs -/

inductive ReadEv (C E : Type) where
  /-- `c` treats the feeling as data: tries an explanation for it -/
  | examine (c : C) (e : E)
  /-- the feeling reads as itself -/
  | recognise (c : C) (e : E)
  /-- `c` says or acts on the feeling as a want -/
  | own (c : C) (e : E)
  deriving DecidableEq, Repr

section reading
variable [AffectReading C E K]

def examinedCount (w : W) (c : C) (e : E) : Nat :=
  ((examined w).find? fun (c', e', _) => c' == c && e' == e).map (·.2.2) |>.getD 0

/-- `c` takes `e` as itself: never an anomaly to them, or recognised. -/
def readAs (w : W) (c : C) (e : E) : Bool :=
  (AffectReading.anomaly (K := K) c e).isNone || (recognised w).contains (c, e)

def ReadEv.ok (w : W) : ReadEv C E → Bool
  | .examine c e => feels w c e > 0
  | .recognise c e => feels w c e > 0 &&
    match AffectReading.anomaly (K := K) c e with
    | some n => examinedCount w c e ≥ n
    | none => true
  | .own c e => feels w c e > 0 && readAs (K := K) w c e

def ReadEv.step (w : W) : ReadEv C E → W
  | .examine c e => setExamined w ((c, e, examinedCount w c e + 1) ::
      (examined w).filter fun (c', e', _) => !(c' == c && e' == e))
  | .recognise c e => if (recognised w).contains (c, e) then w else setRecognised w ((c, e) :: recognised w)
  | .own _ _ => w

def ReadEv.why (w : W) : ReadEv C E → String
  | .examine _ _ => "there is no such feeling to examine (yet)"
  | .recognise c e =>
    if feels w c e == 0 then "there is no such feeling to recognise (yet)" else
    match AffectReading.anomaly (K := K) c e with
    | some n => s!"out of character: they take this feeling as an anomaly to explain; to justify it, first establish: " ++
      s!"they examine it (tried {examinedCount w c e} of {n} explanations)"
    | none => ""
  | .own c e =>
    if feels w c e == 0 then "there is no such feeling to act on (yet)"
    else "out of character: they still take this feeling as an anomaly, a datum, not a want; " ++
      "to justify it, first establish: they recognise it (examine, then recognise)"

instance : Domain W (ReadEv C E) where
  ok := ReadEv.ok (K := K)
  step := ReadEv.step
  why := ReadEv.why (K := K)

/-- A feeling that is the sign of a need can be felt only where the need is felt. -/
def signOk [HasNeeds W C K] [CareSight C K] (w : W) (c : C) (e : E) : Bool :=
  match AffectReading.signals (C := C) e with
  | some k => felt w c c k
  | none => true

/-- An anomaly does not read as itself until it is examined enough. -/
theorem recognise_needs_examination (w : W) (c : C) (e : E) (n : Nat)
    (h : AffectReading.anomaly (K := K) c e = some n) (hn : examinedCount w c e < n) :
    ReadEv.ok (K := K) w (.recognise c e) = false := by
  simp [ReadEv.ok, h]; omega

/-- Nor can it be owned as a want before it reads as itself. -/
theorem own_needs_reading (w : W) (c : C) (e : E) (h : readAs (K := K) w c e = false) :
    ReadEv.ok (K := K) w (.own c e) = false := by
  simp [ReadEv.ok, h]

/-- A sign of a need one is blind to in oneself, and never noticed, is never felt:
being told of the need does not make it felt. -/
theorem feel_sign_blind [HasNeeds W C K] [CareSight C K]
    (w : W) (c : C) (e : E) (k : K)
    (hs : AffectReading.signals (C := C) e = some k) (hb : CareSight.blind c c k = true)
    (hr : (HasNeeds.registered w).contains (c, c, k, true) = false) :
    signOk w c e = false := by
  simp_all [signOk, felt]

end reading

/-! ## Feelings that need a bond first

Some feelings arise only out of a bond: for a demisexual character, desire
appears only toward someone she is already close to. `AffectBond.needs c e =
some (r, n)` says `c` can feel `e` only while she holds tie `r` at level `n` or
more toward someone. Nobody's feelings need a bond by default (`bondOk_free`);
where one does, a feeling shown before the bond is out of character
(`bond_no_feel`), whatever else is happening. -/

class AffectBond (C E R : Type) where
  needs : C → E → Option (R × Nat) := fun _ _ => none

instance (priority := low) {C E R : Type} : AffectBond C E R := {}

section bond
variable [HasTies W C R] [AffectBond C E R]

/-- `c` may feel `e`: no bond needed, or `c` holds the tie at the level toward one of `others`. -/
def bondOk (others : List C) (w : W) (c : C) (e : E) : Bool :=
  match AffectBond.needs c e with
  | some (r, n) => others.any fun d => d != c && HasTies.tie w r c d ≥ n
  | none => true

theorem bondOk_free (others : List C) (w : W) (c : C) (e : E)
    (h : AffectBond.needs (R := R) c e = none) : bondOk (R := R) others w c e = true := by
  simp [bondOk, h]

/-- Before the bond, the feeling is ruled out. -/
theorem bond_no_feel (others : List C) (w : W) (c : C) (e : E) (r : R) (n : Nat)
    (h : AffectBond.needs c e = some (r, n)) (hlow : ∀ d ∈ others, HasTies.tie w r c d < n) :
    bondOk others w c e = false := by
  simp only [bondOk, h, List.any_eq_false]
  intro d hd
  have := hlow d hd
  simp; omega

end bond

end LangLib.World
