import LangLib.World.Mind
import LangLib.World.Social

/-!
# Example: late at the office (space + minds + relationships, told out of order)

Kiran is shy but drawn to Marcus; Marcus is confident. Earlier in the evening
Marcus left a letter on his desk; now he and Kiran are on the roof. While they
talk, Mara (in the office) takes the letter. The text opens on the roof, cuts
to Mara "meanwhile", and only at the end flashes back to Marcus leaving the
letter.

Proved below:
* the story is valid in chronological order, and its timeline satisfies what
  the text says about when (`story_valid`);
* the text's order is not the chronological one (`told_out_of_order`);
* without Kiran's agreement the kiss is not allowed (`kiss_needs_consent`);
* Kiran flirting before Marcus does is out of character (`kiran_wont_flirt_first`);
* Marcus ends up believing the letter is still in the office, which is false
  (`marcus_false_belief`); Mara knows she has it; Mara never learns of the kiss;
* contradictory "when" claims have no timeline at all (`flashback_contradiction`).
-/

namespace LangLib.World.Office
open LangLib.World

inductive Ch | kiran | marcus | mara deriving DecidableEq, Repr
inductive Pl | office | roof deriving DecidableEq, Repr
inductive Ob | letter deriving DecidableEq, Repr
open Ch Pl Ob

abbrev Fact := SpaceFact Ch Pl Ob ⊕ SocialFact Ch

structure W where
  loc : Ch → Pl
  holder : Ob → Option Ch
  objLoc : Ob → Pl
  beliefs : Ch → List (Held Ch Fact)
  bond : Ch → Ch → Dim → Nat
  consent : List (Ch × Ch × Act)

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
  consent := W.consent
  setConsent w cs := { w with consent := cs }

def persona : Ch → Persona
  | kiran => { traits := [.shy, .romantic], values := [.desire, .safety, .pride] }
  | marcus => { traits := [.confident], values := [.desire, .pride, .safety] }
  | mara => { traits := [.secretive], values := [.curiosity, .loyalty] }

instance : HasPersona W Ch := ⟨fun _ => persona⟩
instance : Cast Ch := ⟨[kiran, marcus, mara]⟩

abbrev E := SpaceEv Ch Pl Ob ⊕ MindEv Ch Fact ⊕ SocialEv Ch

instance : DecidableEq E :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)

def sp (e : SpaceEv Ch Pl Ob) : E := ev e
def so (e : SocialEv Ch) : E := ev e
def fact (f : SpaceFact Ch Pl Ob) : Fact := ev f

def start : W where
  loc | kiran => roof | _ => office
  holder _ := some marcus
  objLoc _ := office
  beliefs | kiran => [] | _ => [⟨.atom (fact (.holds marcus letter)), .seen⟩]
  bond
    | kiran, marcus, .attraction => 1 | kiran, marcus, .trust => 1
    | marcus, kiran, .attraction => 2 | marcus, kiran, .trust => 2
    | _, _, _ => 0
  consent := []

/-- Events in the order the text tells them. -/
def told : List E :=
  [ so (.confide marcus kiran),        -- 0  on the roof, Marcus opens up
    so (.flirt marcus kiran),          -- 1
    so (.flirt kiran marcus),          -- 2
    sp (.take mara letter),            -- 3  meanwhile, in the office
    so (.ask marcus kiran .kiss),      -- 4
    so (.agree kiran marcus .kiss),    -- 5
    so (.agree marcus kiran .kiss),    -- 6
    so (.act kiran marcus .kiss),      -- 7
    sp (.drop marcus letter),          -- 8  flashback: earlier, he had left the letter
    sp (.move marcus roof) ]           -- 9  and come up to the roof

def sameTime : List Allen :=
  [.overlaps, .overlappedBy, .during, .contains, .starts, .startedBy, .finishes, .finishedBy, .equal]

/-- What the text says about when. -/
def constraints : List Constraint :=
  [ ⟨8, [.before, .meets], 9⟩, ⟨9, [.before, .meets], 0⟩,   -- the flashback happened first
    ⟨0, [.before, .meets], 1⟩, ⟨1, [.before, .meets], 2⟩,
    ⟨3, sameTime, 1⟩,                                       -- "meanwhile"
    ⟨2, [.before, .meets], 4⟩, ⟨4, [.before, .meets], 5⟩,
    ⟨5, [.equal], 6⟩, ⟨6, [.before, .meets], 7⟩ ]

def story : Timed E :=
  { told, constraints,
    timeline := [⟨2, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩, ⟨3, 6⟩, ⟨6, 7⟩, ⟨7, 8⟩, ⟨7, 8⟩, ⟨8, 9⟩, ⟨0, 1⟩, ⟨1, 2⟩] }

theorem story_valid : story.Valid start := by decide +kernel

theorem told_out_of_order : story.chrono ≠ story.told := by decide +kernel

def ends : W := Timed.stateAt start story 9

/-- Marcus never saw Mara take the letter. -/
theorem marcus_false_belief :
    falseBelief ends marcus (fact (.objAt letter office)) = true := by decide +kernel

theorem mara_knows : knows ends mara (fact (.holds mara letter)) = true := by decide +kernel

/-- The kiss happened on the roof; Mara was in the office. -/
theorem mara_never_saw_kiss :
    believes ends mara (.atom (ev (SocialFact.did kiran marcus .kiss) : Fact)) = false := by
  decide +kernel

theorem kiran_saw_kiss :
    believes ends kiran (.atom (ev (SocialFact.did kiran marcus .kiss) : Fact)) = true := by
  decide +kernel

/-- While Mara takes the letter, Kiran is on the roof the whole time. -/
theorem kiran_on_roof_meanwhile :
    Timed.during start story 3 (fun w => HasLoc.loc w kiran == roof) = true := by decide +kernel

/-- The same events, without Kiran's agreement. -/
def noConsent : List E := story.chrono.filter (· != so (.agree kiran marcus .kiss))

theorem kiss_needs_consent : ¬ Valid start noConsent := by decide +kernel

/-- Right after Marcus confides, before he flirts, Kiran is not yet drawn
enough to overcome her shyness. -/
theorem kiran_wont_flirt_first :
    ¬ Valid start [sp (.drop marcus letter), sp (.move marcus roof), so (.confide marcus kiran),
                   so (.flirt kiran marcus)] := by decide +kernel

/-- Claiming the flashback is both before and after the scene is inconsistent. -/
theorem flashback_contradiction :
    ¬ Consistent 2 [⟨0, [.before], 1⟩, ⟨1, [.before], 0⟩] := by
  rintro ⟨t, -, hp, h⟩
  have h₁ := h _ (List.mem_cons_self ..)
  have h₂ := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨a, b, ha, hb, r, hr, hab⟩ := h₁
  obtain ⟨b', a', hb', ha', r', hr', hba⟩ := h₂
  simp only [List.mem_singleton] at hr hr'
  subst hr hr'
  simp only [Timeline.get?] at ha hb ha' hb'
  rw [ha] at ha'; rw [hb] at hb'
  cases ha'; cases hb'
  simp only [Allen.Holds] at hab hba
  have pa := hp a (List.mem_of_getElem? ha)
  have pb := hp b (List.mem_of_getElem? hb)
  simp only [Interval.Proper] at pa pb
  omega

/--
info: [(7,
  "out of character (shy people hold back); to justify it, first establish: attraction draws them on or the confident make the first move")]
-/
#guard_msgs in
#eval [(7, Domain.why (run start [sp (.drop marcus letter), sp (.move marcus roof),
    so (.confide marcus kiran)]) (so (.flirt kiran marcus)))]

end LangLib.World.Office
