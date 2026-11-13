import LangLib.World.Derive
import LangLib.World.Mind
import LangLib.World.Social

/-!
# Example: who read the letter (evidence, trust, ranked beliefs)

The lore: whoever holds the letter has read it. Theo watches Mara pick the
letter up in the office; Kiran is on the roof. Mara goes up and swears to Kiran
she never read it. Kiran, gullible and fond of Mara, believes her, until she
sees Mara with the letter. Then Theo, skeptical and wary of Mara, comes up
and hears the same lie.

How each takes the lie depends on who they are and whom they trust
(`socialCredence`): to Kiran it is strong testimony from a trusted friend
(radical upgrade); to Theo it is barely worth noting.

Proved below:
* Theo infers Mara read the letter (`theo_infers`);
* Kiran believes the lie, then sees the letter and stops, without forgetting
  it was said (`kiran_believed_the_lie`, `kiran_caught_the_lie`,
  `nothing_forgotten`), and her trust in Mara drops (`kiran_trusts_mara_less`);
* Theo only notes that Mara said it (`theo_only_notes`);
* "Kiran realised Mara had read it" is a knowledge leak before she saw the
  letter and fine after (`realise_too_early`, `realise_after_seeing`);
* views are consistent by construction (`Mind.view_consistent`).
-/

namespace LangLib.World.Gossip
open LangLib.World

inductive Ch | kiran | theo | mara deriving DecidableEq, Repr
inductive Pl | office | roof deriving DecidableEq, Repr
inductive Ob | letter deriving DecidableEq, Repr
inductive Secret | read (c : Ch) deriving DecidableEq, Repr
open Ch Pl Ob

inductive Fact | space (x : SpaceFact Ch Pl Ob) | secret (x : Secret)
  deriving DecidableEq, Repr, StoryFact

def holds (c : Ch) : Fact := ev (SpaceFact.holds c letter : SpaceFact Ch Pl Ob)
def read (c : Ch) : Fact := ev (Secret.read c)

instance : Lore Fact := ⟨[kiran, theo, mara].map fun c => ⟨[(holds c, true)], (read c, true)⟩⟩

structure W where
  loc : Ch → Pl
  holder : Ob → Option Ch
  objLoc : Ob → Pl
  beliefs : Ch → List (Held Ch Fact)
  bond : Ch → Ch → Dim → Nat
  clock : Nat := 0
  /-- Kiran does not trust Mara about secrets -/
  wary : Bool := false

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
  | theo => { traits := [.skeptical], values := [.honesty, .safety] }
  | mara => { traits := [.secretive], values := [.curiosity] }

instance : HasPersona W Ch := ⟨fun _ => persona⟩
instance : Cast Ch := ⟨[kiran, theo, mara]⟩
instance : Truth W Secret := ⟨fun _ s => match s with | .read c => c == mara⟩
instance : Clock W := ⟨W.clock, fun w => { w with clock := w.clock + 1 }⟩

instance : TopicTrust W Ch Fact where
  topical w c d l := match c, d, l.1 with
    | kiran, mara, .secret _ => if w.wary then some ("not to be trusted about secrets", -5) else none
    | _, _, _ => none

instance : Credence W Ch Fact := socialCredence

inductive E | space (x : SpaceEv Ch Pl Ob) | mind (x : MindEv Ch Fact)
  deriving DecidableEq, Repr, StoryEvent

def sp (e : SpaceEv Ch Pl Ob) : E := ev e
def mi (e : MindEv Ch Fact) : E := ev e

def start : W :=
  { loc | kiran => roof | _ => office, holder := fun _ => none, objLoc := fun _ => office,
    beliefs := fun _ => [],
    bond | kiran, mara, .trust => 2 | theo, kiran, .trust => 2 | _, _, _ => 0 }

def act1 : List E := [sp (.take mara letter), sp (.move mara roof)]
def act2 : List E := [mi (.lie mara kiran (read mara, false))]
def act3 : List E := [sp (.drop mara letter), sp (.take mara letter)]
def act4 : List E := [sp (.move theo roof), mi (.lie mara theo (read mara, false))]
def story : List E := act1 ++ act2 ++ act3 ++ act4

theorem story_valid : Valid start story := by decide +kernel

theorem theo_infers : thinks (run start act1) theo (read mara) = true := by decide +kernel

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
theorem theo_only_notes :
    let w := run start story
    thinks w theo (read mara) = true ∧
    (HasMinds.beliefs w theo).any (fun h => h.b == .neg (read mara) && h.up != .note) = false ∧
    believes w theo (.bel mara (.neg (read mara))) = true := by decide +kernel

/-- Kiran cannot realise Mara read the letter while she believes the lie. -/
theorem realise_too_early :
    ¬ Valid start (act1 ++ act2 ++ [mi (.realise kiran (read mara, true))]) := by decide +kernel

theorem realise_after_seeing :
    Valid start (act1 ++ act2 ++ act3 ++ [mi (.realise kiran (read mara, true))]) := by
  decide +kernel

/-- info: some (3, "they have no way to know that") -/
#guard_msgs in
#eval firstFailure start (act1 ++ act2 ++ [mi (.realise kiran (read mara, true))]) 0

/-! ## Why: explanations -/

/--
info: ["not LangLib.World.Gossip.Fact.secret (LangLib.World.Gossip.Secret.read (LangLib.World.Gossip.Ch.mara)) (prior for being told +3, trusts the speaker +1, gullible +1 = 5; LangLib.World.Upgrade.radical): outranked by LangLib.World.Gossip.Fact.secret (LangLib.World.Gossip.Secret.read (LangLib.World.Gossip.Ch.mara))"]
-/
#guard_msgs in
#eval explain (run start (act1 ++ act2 ++ act3)) kiran (read mara, false)

/-! ## Trust by topic -/

/-- Kiran trusts Mara, but not about secrets: the same lie is only noted. -/
def wary : W := { start with wary := true }

theorem wary_kiran_only_notes :
    let w := run wary (act1 ++ act2)
    thinksNot w kiran (read mara) = false ∧
    believes w kiran (.bel mara (.neg (read mara))) = true := by decide +kernel

/-! ## Past and present

Theo goes back down. Mara leaves the letter on the roof, where Kiran sees it.
Kiran goes down and tells Theo. Theo saw Mara holding the letter (time 0);
Kiran's newer word (he trusts her) is about now. He comes to think the letter is
on the roof now, still thinks Mara held it then, and still thinks she read it. -/

def lies : Fact := ev (SpaceFact.objAt letter roof : SpaceFact Ch Pl Ob)
def act5 : List E := [sp (.move theo office), sp (.drop mara letter), sp (.move kiran office),
                      mi (.tell kiran theo (lies, true))]
def later : List E := story ++ act5

theorem later_valid : Valid start later := by decide +kernel

theorem theo_now_and_then :
    let w := run start later
    thinks w theo lies = true ∧            -- now: on the roof (Kiran said so)
    thinks w theo (holds mara) = false ∧   -- no longer in Mara's hand
    thinksWas w theo (holds mara) 0 = true ∧ -- but at time 0 it was
    thinks w theo (read mara) = true := by  -- and reading it is permanent
  decide +kernel

/-! ## Beliefs over time: "I believed that then" -/

/-- At time 3 (after the lie) Kiran believed Mara had not read it; now she
believes she had, and can recall that she once believed otherwise. -/
theorem kiran_remembers_believing :
    let w := run start later
    believedAt w kiran 3 (read mara, false) = true ∧ thinks w kiran (read mara) = true := by
  decide +kernel

end LangLib.World.Gossip
