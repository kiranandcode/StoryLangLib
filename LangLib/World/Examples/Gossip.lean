import LangLib.World.Mind

/-!
# Example: who read the letter (belief reasoning, revision, rejection)

The lore: whoever holds the letter has read it. Marcus watches Mara pick the
letter up in the office; Kiran is on the roof. Mara goes up and swears to Kiran
she never read it. Kiran believes her, until she sees Mara with the letter.
Then Marcus comes up and Mara tries the same lie on him; he saw her take it, so
he rejects it.

Proved below (minds are kept consistent by an `Invariant`, so `Valid` itself
says no one ever believes a contradiction):
* Marcus infers Mara read the letter, which nobody told him (`marcus_infers`);
* Kiran first believes the lie, then drops it on seeing the letter, and ends up
  knowing that Mara lied (`kiran_believed_the_lie`, `kiran_caught_the_lie`);
* Marcus rejects the same lie, noting only that Mara claimed it
  (`marcus_rejects_the_lie`);
* Kiran reasons about Mara's mind: she thinks Mara thinks she has read it
  (`kiran_reads_mara`);
* a mind that starts out contradictory makes every story invalid
  (`contradiction_rejected`).
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

instance : Cast Ch := ⟨[kiran, marcus, mara]⟩
instance : Truth W Secret := ⟨fun _ s => match s with | .read c => c == mara⟩
instance : Invariant W := ⟨mindsConsistent⟩

abbrev E := SpaceEv Ch Pl Ob ⊕ MindEv Ch Fact
instance : DecidableEq E := @instDecidableEqSum _ _ inferInstance inferInstance

def sp (e : SpaceEv Ch Pl Ob) : E := ev e
def mi (e : MindEv Ch Fact) : E := ev e

def start : W :=
  { loc | kiran => roof | _ => office, holder := fun _ => none, objLoc := fun _ => office,
    beliefs := fun _ => [] }

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
    thinks w kiran (read mara) = true ∧ thinksNot w kiran (read mara) = false ∧
    believes w kiran (.bel mara (.neg (read mara))) = true := by decide +kernel

theorem marcus_rejects_the_lie :
    let w := run start story
    thinks w marcus (read mara) = true ∧ thinksNot w marcus (read mara) = false ∧
    believes w marcus (.bel mara (.neg (read mara))) = true := by decide +kernel

theorem kiran_reads_mara :
    thinksThinks (run start (act1 ++ act2 ++ act3)) kiran mara (read mara) = true := by
  decide +kernel

/-- Kiran starts out holding a contradiction (she saw Mara with the letter, and
saw that Mara had not read it): no story from here is valid. -/
def muddled : W :=
  { start with beliefs := fun
      | kiran => [⟨.atom (holds mara), .seen⟩, ⟨.neg (read mara), .seen⟩]
      | _ => [] }

theorem contradiction_rejected : ¬ Valid muddled [sp (.move kiran office)] := by decide +kernel

/-- info: some (0, "it would leave the story inconsistent") -/
#guard_msgs in
#eval firstFailure muddled [sp (.move kiran office)] 0

end LangLib.World.Gossip
