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

end LangLib.World
