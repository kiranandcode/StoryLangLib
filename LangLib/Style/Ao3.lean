import LangLib.Style.Core

namespace LangLib.Style

/-- What two explicit AO3 chapters share (stories/private-ao3-boyremoval, first
person, 43 paragraphs; stories/private-ao3-sweet-girl, close third, present
tense, 95 paragraphs), measured by `langlib style` (records in `Data/`, no
text). Each bound is set at or below the lower of the two values, so both
chapters hold (`Ao3Theorems.lean`); what they do not share (person, fragments,
whether talk rises or falls through a scene) is left out.

* sentences of 11 to 16 words on average (15.8 and 11.4), with both short
  ones (a sixth or more of sentences at most 6 words: 0.18, 0.33) and long ones
  (a twentieth at 25 or more: 0.17, 0.06), and short punches right after long
  sentences (at least one per 60 sentences: 0.017, 0.062);
* talk: an eighth of the words or more in quotes (0.15, 0.39), tagged with
  varied verbs (half or more not "say": 0.5, 0.96);
* close to the point of view: half the clauses with a character for subject
  are the point-of-view character's (0.52, 0.55), with some of them her mind
  (a twentieth: 0.22, 0.07);
* heat by intensifiers (one per seven sentences: 0.36, 0.15) and by repetition
  (one repeated content word per 25 sentences: 0.12, 0.04);
* check-ins as beats: a short quoted question per seven paragraphs (0.16, 0.24). -/
def ao3 : Style where
  name := "ao3"
  rules := [
    ("mean sentence at least 11 words", .ratioAtLeast .words .sents 11 1),
    ("mean sentence at most 16 words", .ratioAtMost .words .sents 16 1),
    ("short sentences", .ratioAtLeast .short .sents 1 6),
    ("long sentences", .ratioAtLeast .long .sents 1 20),
    ("punches after long sentences", .ratioAtLeast .punches .sents 1 60),
    ("dialogue", .ratioAtLeast .quoteWords .words 1 8),
    ("varied tags", .ratioAtLeast .fancyTags .tags 1 2),
    ("close to the point of view", .ratioAtLeast .povClauses .charClauses 1 2),
    ("some interiority", .ratioAtLeast .interior .charClauses 1 20),
    ("intensifiers", .ratioAtLeast .intensifiers .sents 1 7),
    ("repetition", .ratioAtLeast .repeats .sents 1 25),
    ("check-ins", .ratioAtLeast .checkIns .paras 1 7)]

/-- The target for stories/private-roof-ran: the AO3 rhythm and heat, carried
by Kiran's voice from stories/roof. Her interiority is clinical (she logs,
tests, measures what she feels: a clause of it per two paragraphs or more);
the narration stays in close third with no narrator asides (no first person,
generalisations at most one sentence in twenty, no parentheticals). -/
def roofRan : Style where
  name := "roof-ran"
  rules := ao3.rules ++ [
    ("clinical interiority", .ratioAtLeast .clinical .paras 1 2),
    ("close third", .atMost .firstPerson 0),
    ("few generalisations", .ratioAtMost .generics .sents 1 20),
    ("no parentheticals", .atMost .prn 0)]

end LangLib.Style
