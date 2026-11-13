import LangLib.World.Derive

/-!
# Example: a date (unknowns, dialogue, goals and plans)

Kiran is at the bar. The text never says where Theo starts: he simply asks
her whether she is seeing anyone. She says she is single and hints that she
likes him; he answers with sarcasm ("ugh, I can't stand you"), which she reads
correctly because she trusts him. He promises to walk her home; she wants to go
home; both plan the walk and carry it out.

Proved below:
* the story is not *valid* outright, because it never establishes that Theo
  is at the bar, but it is *plausible*, under exactly one assumption
  (`only_one_assumption`);
* the answer, the hint and the sarcasm land as intended (`what_they_learned`);
  without rapport the same sarcasm is taken literally (`stranger_misreads`);
* the question is closed, the promise kept (`promise_kept`);
* every action is motivated by a plan or a goal (`all_motivated`); a stray
  extra move is not (`stray_move`);
* Theo's plan would work from where he made it (`theo_plan_works`).
-/

namespace LangLib.World.Date
open LangLib.World

inductive Ch | kiran | theo deriving DecidableEq, Repr
inductive Pl | bar | street | home deriving DecidableEq, Repr
inductive Info | single (c : Ch) | likes (c d : Ch) deriving DecidableEq, Repr
open Ch Pl

inductive Fact | space (x : SpaceFact Ch Pl Unit) | social (x : SocialFact Ch) | info (x : Info)
  deriving DecidableEq, Repr, StoryFact
inductive A | space (x : SpaceEv Ch Pl Unit) | mind (x : MindEv Ch Fact) | social (x : SocialEv Ch) | dialogue (x : DialogueEv Ch Fact)
  deriving DecidableEq, Repr, StoryEvent
inductive E | action (x : A) | goal (x : GoalEv Ch Fact A)
  deriving DecidableEq, Repr, StoryEvent


structure W where
  loc : Ch → Pl
  known : List Ch
  beliefs : Ch → List (Held Ch Fact)
  bond : Ch → Ch → Dim → Nat
  consent : List (Ch × Ch × Act) := []
  questions : List (Ch × Ch × Fact) := []
  promises : List (Ch × Ch × (Fact × Bool)) := []
  requests : List (Ch × Ch × (Fact × Bool)) := []
  goals : Ch → List (Fact × Bool) := fun _ => []
  plans : Ch → List (Plan A Fact) := fun _ => []
  clock : Nat := 0

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

instance : HasSpace W Ch Pl Unit where
  loc := W.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder _ _ := none
  setHolder w _ _ := w
  objLoc _ _ := .bar
  setObjLoc w _ _ := w

instance : PartialLoc W Ch where
  locKnown w c := w.known.contains c
  assumeAt w a b := { w with loc := upd w.loc a (w.loc b), known := a :: w.known }
  markLoc w c := { w with known := c :: w.known }

instance : HasMinds W Ch Fact := ⟨W.beliefs, fun w c bs => { w with beliefs := upd w.beliefs c bs }⟩
instance : HasBonds W Ch where
  bond := W.bond
  setBond w a b k n := { w with bond := fun x y j => if x = a ∧ y = b ∧ j = k then n else w.bond x y j }
  consent := W.consent
  setConsent w cs := { w with consent := cs }
instance : HasPersona W Ch := ⟨fun _ _ => { traits := [], values := [.desire, .safety] }⟩
instance : HasDialogue W Ch Fact where
  questions := W.questions
  setQuestions w q := { w with questions := q }
  promises := W.promises
  setPromises w p := { w with promises := p }
  requests := W.requests
  setRequests w r := { w with requests := r }
instance : HasGoals W Ch Fact A where
  goals := W.goals
  setGoals w c g := { w with goals := upd w.goals c g }
  plans := W.plans
  setPlans w c p := { w with plans := upd w.plans c p }
instance : Cast Ch := ⟨[kiran, theo]⟩
instance : Clock W := ⟨W.clock, fun w => { w with clock := w.clock + 1 }⟩
instance : Truth W Info := ⟨fun _ i => match i with
  | .single c => c == kiran | .likes _ _ => true⟩
instance : Credence W Ch Fact := socialCredence
instance : Rapport W Ch := bondRapport


def sp (e : SpaceEv Ch Pl Unit) : A := ev e
def dl (e : DialogueEv Ch Fact) : A := ev e
def act (a : A) : E := .action a
def goal (g : GoalEv Ch Fact A) : E := .goal g
def single (c : Ch) : Fact := ev (Info.single c)
def likes (c d : Ch) : Fact := ev (Info.likes c d)
def at_ (c : Ch) (p : Pl) : Fact := ev (SpaceFact.at_ c p : SpaceFact Ch Pl Unit)

def own (f : Fact) : Held Ch Fact := { b := .atom f, src := .self, rank := 10, stamp := 0, up := .hard }

def start : W :=
  { loc := fun _ => bar, known := [kiran],
    beliefs | kiran => [own (single kiran), own (likes kiran theo)] | theo => [own (likes theo kiran)],
    bond | kiran, theo, .trust => 2 | theo, kiran, .trust => 2 | _, _, _ => 0 }

def kiranPlan : Plan A Fact := { goal := (at_ kiran home, true), steps := [sp (.move kiran street), sp (.move kiran home)] }
def theoPlan : Plan A Fact := { goal := (at_ theo home, true), steps := [sp (.move theo street), sp (.move theo home)] }

def story : List E :=
  [ act (dl (.ask theo kiran (single kiran))),
    act (dl (.answer kiran theo (single kiran, true))),
    act (dl (.hint kiran theo (likes kiran theo, true))),
    act (dl (.sarcasm theo kiran (likes theo kiran, true))),
    act (dl (.promise theo kiran (at_ theo home, true))),
    goal (.adopt kiran (at_ kiran home, true)),
    goal (.intend kiran kiranPlan),
    goal (.intend theo theoPlan),
    act (sp (.move kiran street)), act (sp (.move theo street)),
    act (sp (.move kiran home)), act (sp (.move theo home)) ]

theorem not_valid_outright : ¬ Valid start story := by decide +kernel
theorem plausible : Plausible start story := by decide +kernel

theorem only_one_assumption :
    assumptions start story 0 = [(0, "assumes they were together")] := by decide +kernel

def ends : W := run start story

theorem what_they_learned :
    thinks ends theo (single kiran) = true ∧          -- the answer
    thinks ends theo (likes kiran theo) = true ∧    -- the hint
    thinks ends kiran (likes theo kiran) = true := by  -- the sarcasm, read right
  decide +kernel

/-- Someone without rapport takes "I can't stand you" at face value. -/
theorem stranger_misreads :
    let w := run { start with bond := fun _ _ _ => 0 } story
    thinksNot w kiran (likes theo kiran) = true := by decide +kernel

theorem promise_kept : HasDialogue.questions ends = [] ∧ (broken ends).isEmpty = true ∧
    (kept ends).length = 1 := by decide +kernel

theorem all_motivated : unmotivated (S := E) (E := A) start story = [] := by decide +kernel

/-- An extra trip back to the bar serves no goal and no plan. -/
theorem stray_move :
    unmotivated (S := E) (E := A) start (story ++ [act (sp (.move theo bar))]) = [12] := by
  decide +kernel

theorem theo_plan_works :
    planWorks (S := E) (run start (story.take 8)) theoPlan = true := by decide +kernel

/-- Witnessing is on: Kiran, already home, saw Theo arrive. -/
theorem kiran_saw_him_arrive : thinks ends kiran (at_ theo home) = true := by decide +kernel

end LangLib.World.Date
