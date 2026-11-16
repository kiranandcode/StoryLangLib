import LangLib.Style.Ao3

namespace LangLib.Style

/-- The target for the Fixpoint series (a slow-burn romance in Kiran's point of
view): AO3's rhythm and patterns (`ao3`: sentence lengths with short punches
after long ones, varied tags, interiority, check-ins as beats), carried by
Kiran's own voice as she types and talks it:

* analytical: her interiority is clinical, logged and tested (a clause of it per
  two paragraphs or more), as in `roofRan`;
* cutesy and quick: play in the talk, interjections and exclamation marks inside
  quotes ("Ooh", "wait", "yes!"), at least one per three paragraphs;
* banter carries the burn: a fifth of the words or more in quotes, more than
  AO3's eighth;
* close third, no narrator standing outside her: no first person in narration,
  generalisations at most one sentence in twenty, no parentheticals. -/
def fixpoint : Style where
  name := "fixpoint"
  rules := ao3.rules ++ [
    ("clinical interiority", .ratioAtLeast .clinical .paras 1 2),
    ("playful talk", .ratioAtLeast .playful .paras 1 3),
    ("banter", .ratioAtLeast .quoteWords .words 1 5),
    ("close third", .atMost .firstPerson 0),
    ("few generalisations", .ratioAtMost .generics .sents 1 20),
    ("no parentheticals", .atMost .prn 0)]

end LangLib.Style
