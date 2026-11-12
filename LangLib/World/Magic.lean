import LangLib.World.Space

/-!
# A magic system (example of a story-specific module)

Characters know some spells and have a mana pool. Casting costs mana and needs
the target present; resting restores it. A cast is seen by everyone present,
who learn that the caster can cast that spell (`MagicFact.canCast`): a secret
power stays secret until used in front of someone.
-/

namespace LangLib.World

inductive Spell | light | ward | heal | glamour
  deriving DecidableEq, Repr

def Spell.cost : Spell → Nat
  | .light => 1 | .ward => 3 | .heal => 2 | .glamour => 2

class HasMana (W : Type) (C : outParam Type) where
  mana : W → C → Nat
  setMana : W → C → Nat → W
  maxMana : W → C → Nat
  spells : W → C → List Spell

inductive MagicEv (C : Type) where
  | cast (c : C) (s : Spell) (t : C)
  | rest (c : C)
  deriving DecidableEq, Repr

inductive MagicFact (C : Type) where
  | canCast (c : C) (s : Spell)
  deriving DecidableEq, Repr

variable {W C P : Type} [DecidableEq C] [DecidableEq P] [HasLoc W C P] [HasMana W C]
open HasLoc HasMana

instance : Domain W (MagicEv C) where
  ok w
    | .cast c s t => (spells w c).contains s && s.cost ≤ mana w c && loc w c == loc w t
    | .rest _ => true
  step w
    | .cast c s _ => setMana w c (mana w c - s.cost)
    | .rest c => setMana w c (maxMana w c)
  why w
    | .cast c s t =>
      if !(spells w c).contains s then "they do not know that spell"
      else if s.cost > mana w c then s!"not enough mana ({mana w c} < {s.cost})"
      else if loc w c != loc w t then "the target is not there" else ""
    | .rest _ => ""

instance : Truth W (MagicFact C) where
  truth w | .canCast c s => (spells w c).contains s

instance {Φ : Type} [Inject (MagicFact C) Φ] : Observable W (MagicEv C) Φ P where
  seen w
    | .cast c s _ => some (loc w c, [ev (MagicFact.canCast c s)])
    | .rest _ => none

end LangLib.World
