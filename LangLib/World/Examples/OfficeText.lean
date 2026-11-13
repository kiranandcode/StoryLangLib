import LangLib.Json
import LangLib.Check
import LangLib.World.Lexicon
import LangLib.World.Examples.Office

/-!
# The office story, from text

`examples/office.txt` was annotated by Opus (eval/prompt.md) and accepted by
`langlib check`. Reading it with the space and relationship lexicons gives the
office story's events in the order the text tells them, and its adverbials
("Meanwhile", "An hour earlier") give the constraints on when; the solver finds
a timeline in minutes, and the story is valid.
-/

namespace LangLib.World.Office
open LangLib LangLib.Scene Ch Pl Ob

def resolver : Resolver Ch Pl Ob where
  char | "kiran" => some .kiran | "theo" => some .theo | "mara" => some .mara | _ => none
  place | "office" => some .office | "roof" => some .roof | _ => none
  obj | "letter" => some .letter | _ => none

def lexicon : Lexicon E := (spaceLex resolver).inj ++ (socialLex resolver).inj

def passage : String := include_str "../../../examples/office.txt"
def annotated : String := include_str "../../../examples/office.json"

def textDoc : Doc := (docOfString annotated).toOption.getD {}

#guard (check passage textDoc).ok
#guard (lexicon.story textDoc).told == told

/-- The story as read off the text, with the solver's timeline (minutes). -/
def fromText : Timed E :=
  { told,
    constraints :=
      [⟨0, [.before, .meets], 1⟩, ⟨1, [.before, .meets], 2⟩, ⟨2, [.before, .meets], 4⟩,
       ⟨4, [.before, .meets], 5⟩, ⟨5, [.before, .meets], 6⟩, ⟨6, [.before, .meets], 7⟩,
       ⟨8, [.before, .meets], 9⟩, ⟨9, [.before, .meets], 0⟩, ⟨3, World.sameTime, 2⟩],
    metric := [.gap 8 0 50 70],
    timeline := [⟨51, 52⟩, ⟨53, 54⟩, ⟨55, 58⟩, ⟨56, 57⟩, ⟨59, 60⟩, ⟨61, 62⟩, ⟨63, 64⟩,
                 ⟨65, 66⟩, ⟨0, 1⟩, ⟨2, 3⟩] }

-- the text yields exactly these constraints, and the solver this timeline
#guard (lexicon.story textDoc).constraints == fromText.constraints
#guard (lexicon.story textDoc).metric == fromText.metric
#guard (lexicon.story textDoc).solved.map (·.timeline) == some fromText.timeline

theorem fromText_valid : fromText.Valid start := by decide +kernel

/-- "An hour earlier": Theo left the letter between 50 and 70 minutes before
the scene opens. -/
theorem an_hour_earlier : ∃ a b, fromText.timeline[8]? = some a ∧ fromText.timeline[0]? = some b ∧
    50 ≤ b.s - a.e ∧ b.s - a.e ≤ 70 := ⟨_, _, rfl, rfl, by decide, by decide⟩

/-- Theo still ends up wrong about the letter. -/
theorem fromText_false_belief :
    falseBelief (Timed.stateAt start fromText 66) theo (fact (.objAt letter office)) = true := by
  decide +kernel

end LangLib.World.Office
