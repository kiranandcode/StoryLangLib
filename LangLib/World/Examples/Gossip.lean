import LangLib.World.Mind
import LangLib.World.Social

/-!
# Example: who read the letter (evidence, trust, ranked beliefs)

The lore: whoever holds the letter has read it. Marcus watches Mara pick the
letter up in the office; Kiran is on the roof. Mara goes up and swears to Kiran
she never read it. Kiran, gullible and fond of Mara, believes her, until she
sees Mara with the letter. Then Marcus, skeptical and wary of Mara, comes up
and hears the same lie.

How each takes the lie depends on who they are and whom they trust
(`socialCredence`): to Kiran it is strong testimony from a trusted friend
(radical upgrade); to Marcus it is barely worth noting.

Proved below:
* Marcus infers Mara read the letter (`marcus_infers`);
* Kiran believes the lie, then sees the letter and stops, without forgetting
  it was said (`kiran_believed_the_lie`, `kiran_caught_the_lie`,
  `nothing_forgotten`), and her trust in Mara drops (`kiran_trusts_mara_less`);
* Marcus only notes that Mara said it (`marcus_only_notes`);
* "Kiran realised Mara had read it" is a knowledge leak before she saw the
  letter and fine after (`realise_too_early`, `realise_after_seeing`);
* views are consistent by construction (`Mind.view_consistent`).
-/

namespace LangLib.World.Gossip
open LangLib.World

inductive Ch | kiran | marcus | mara deriving DecidableEq, Repr
inductive Pl | office | roof deriving DecidableEq, Repr
inductive Ob | letter deriving DecidableEq, Repr
inductive Secret | read (c : Ch) deriving DecidableEq, Repr
open Ch Pl Ob

abbrev Fact := SpaceFact Ch Pl Ob ⊕ Secret

def holds (c : Ch) : Fact := ev (SpaceFact.holds c letter : SpaceFact Ch Pl Ob)
def read (c : Ch) : Fact := ev (Secret.read c)

instance : Lore Fact := ⟨[kiran, marcus, mara].map fun c => ⟨[(holds c, true)], (read c, true)⟩⟩

structure W where
  loc : Ch → Pl
  holder : Ob → Option Ch
  objLoc : Ob → Pl
  beliefs : Ch → List (Held Ch Fact)
  bond : Ch → Ch → Dim → Nat

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

instance : HasSpace W Ch Pl Ob where
  loc := W.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder := W.holder
  setHolder w o h := { w with holder := upd w.holder o h }
  objLoc := W.objLoc
  setObjLoc w o p := { w with objLoc := upd w.objLoc o p }

instance : HasMinds W Ch Fact where
  beliefs := W.beliefs
  setBeliefs w c bs := { w with beliefs := upd w.beliefs c bs }

instance : HasBonds W Ch where
  bond := W.bond
  setBond w a b k n := { w with bond := fun x y j => if x = a ∧ y = b ∧ j = k then n else w.bond x y j }
  consent _ := []
  setConsent w _ := w

def persona : Ch → Persona
  | kiran => { traits := [.gullible], values := [.loyalty, .safety] }
  | marcus => { traits := [.skeptical], values := [.honesty, .safety] }
  | mara => { traits := [.secretive], values := [.curiosity] }

instance : HasPersona W Ch := ⟨fun _ => persona⟩
instance : Cast Ch := ⟨[kiran, marcus, mara]⟩
instance : Truth W Secret := ⟨fun _ s => match s with | .read c => c == mara⟩
instance : Credence W Ch := socialCredence

abbrev E := SpaceEv Ch Pl Ob ⊕ MindEv Ch Fact
instance : DecidableEq E := @instDecidableEqSum _ _ inferInstance inferInstance

def sp (e : SpaceEv Ch Pl Ob) : E := ev e
def mi (e : MindEv Ch Fact) : E := ev e

def start : W :=
  { loc | kiran => roof | _ => office, holder := fun _ => none, objLoc := fun _ => office,
    beliefs := fun _ => [],
    bond | kiran, mara, .trust => 2 | _, _, _ => 0 }

def act1 : List E := [sp (.take mara letter), sp (.move mara roof)]
def act2 : List E := [mi (.lie mara kiran (read mara, false))]
def act3 : List E := [sp (.drop mara letter), sp (.take mara letter)]
def act4 : List E := [sp (.move marcus roof), mi (.lie mara marcus (read mara, false))]
def story : List E := act1 ++ act2 ++ act3 ++ act4

theorem story_valid : Valid start story := by decide +kernel

theorem marcus_infers : thinks (run start act1) marcus (read mara) = true := by decide +kernel

theorem kiran_believed_the_lie :
    thinksNot (run start (act1 ++ act2)) kiran (read mara) = true := by decide +kernel

theorem kiran_caught_the_lie :
    let w := run start (act1 ++ act2 ++ act3)
    thinks w kiran (read mara) = true ∧ thinksNot w kiran (read mara) = false := by decide +kernel

/-- The lie is still in her evidence base, just outranked; and she remembers Mara said it. -/
theorem nothing_forgotten :
    let w := run start (act1 ++ act2 ++ act3)
    believes w kiran (.neg (read mara)) = true ∧
    believes w kiran (.bel mara (.neg (read mara))) = true := by decide +kernel

theorem kiran_trusts_mara_less :
    HasBonds.bond (run start (act1 ++ act2 ++ act3)) kiran mara .trust = 1 := by decide +kernel

/-- To a skeptic who does not trust Mara, her word is only noted. -/
theorem marcus_only_notes :
    let w := run start story
    thinks w marcus (read mara) = true ∧
    (HasMinds.beliefs w marcus).any (fun h => h.b == .neg (read mara) && h.up != .note) = false ∧
    believes w marcus (.bel mara (.neg (read mara))) = true := by decide +kernel

/-- Kiran cannot realise Mara read the letter while she believes the lie. -/
theorem realise_too_early :
    ¬ Valid start (act1 ++ act2 ++ [mi (.realise kiran (read mara, true))]) := by decide +kernel

theorem realise_after_seeing :
    Valid start (act1 ++ act2 ++ act3 ++ [mi (.realise kiran (read mara, true))]) := by
  decide +kernel

/-- info: some (3, "they have no way to know that") -/
#guard_msgs in
#eval firstFailure start (act1 ++ act2 ++ [mi (.realise kiran (read mara, true))]) 0

end LangLib.World.Gossip
