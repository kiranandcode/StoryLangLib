import LangLib.World.Mind
import LangLib.World.Magic

/-!
# Example: a secret mage (space + minds + a magic system)

The same framework with a different module set: no relationships, but a power
system. Kiran can cast `light` and `ward`; nobody knows. She wards herself
alone in the tower, goes down to the hall, and lights a lamp for Marcus, who
now knows she can cast light, but still not that she can ward. Trying to ward
again before resting fails: she is out of mana.
-/

namespace LangLib.World.Mage
open LangLib.World

inductive Ch | kiran | marcus deriving DecidableEq, Repr
inductive Pl | tower | hall deriving DecidableEq, Repr
abbrev Fact := SpaceFact Ch Pl Unit ⊕ MagicFact Ch

structure W where
  loc : Ch → Pl
  beliefs : Ch → List (Held Ch Fact)
  mana : Ch → Nat

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

instance : HasSpace W Ch Pl Unit where
  loc := W.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder _ _ := none
  setHolder w _ _ := w
  objLoc _ _ := .tower
  setObjLoc w _ _ := w

instance : HasMinds W Ch Fact where
  beliefs := W.beliefs
  setBeliefs w c bs := { w with beliefs := upd w.beliefs c bs }

instance : HasMana W Ch where
  mana := W.mana
  setMana w c n := { w with mana := upd w.mana c n }
  maxMana _ | .kiran => 4 | .marcus => 0
  spells _ | .kiran => [.light, .ward] | .marcus => []

instance : Cast Ch := ⟨[.kiran, .marcus]⟩

abbrev E := SpaceEv Ch Pl Unit ⊕ MindEv Ch Fact ⊕ MagicEv Ch
instance : DecidableEq E :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)

open Ch Pl
def mg (e : MagicEv Ch) : E := ev e
def sp (e : SpaceEv Ch Pl Unit) : E := ev e
def canCast (c : Ch) (s : Spell) : Fact := ev (MagicFact.canCast c s)

def start : W := { loc | kiran => tower | marcus => hall, beliefs := fun _ => [], mana := fun _ => 4 }

def story : List E :=
  [mg (.cast kiran .ward kiran), sp (.move kiran hall), mg (.cast kiran .light marcus)]

theorem story_valid : Valid start story := by decide +kernel

def ends : W := run start story

theorem marcus_knows_light : knows ends marcus (canCast kiran .light) = true := by decide +kernel

/-- She warded herself alone, so her other power is still a secret. -/
theorem ward_still_secret : believes ends marcus (.atom (canCast kiran .ward)) = false := by
  decide +kernel

/-- Ward costs 3, light 1: from 4 mana there is none left for a second ward. -/
theorem no_second_ward : ¬ Valid start (story ++ [mg (.cast kiran .ward kiran)]) := by
  decide +kernel

theorem rest_then_ward :
    Valid start (story ++ [mg (.rest kiran), mg (.cast kiran .ward kiran)]) := by decide +kernel

/-- info: some (3, "not enough mana (0 < 3)") -/
#guard_msgs in
#eval firstFailure start (story ++ [mg (.cast kiran .ward kiran)]) 0

end LangLib.World.Mage
