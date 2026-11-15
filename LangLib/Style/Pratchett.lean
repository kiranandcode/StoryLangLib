import LangLib.Style.Core

namespace LangLib.Style

/-- Terry Pratchett's manner, as far as checked trees show it.

Calibrated on `stories/roof-pratchett` (8 footnotes in 9 paragraphs, 54
generic clauses in 90 sentences, 8 "like" similes, 9 Concepts, 62 narrator
asides against 12 clauses of her mind) and `stories/roof` (none of these),
with each threshold set well inside the gap:

* footnotes: at least one per two paragraphs, each anchored once to a sentence
  that stands without it, each one a generalisation, and together brief (the
  aside is not the story);
* the narrator generalises: a quarter of sentences hold a present-tense generic
  ("People do.");
* similes: a "like" simile per two paragraphs;
* capitalised Concepts (Deadlines, Great Truths, Love): one per two paragraphs;
* asides outnumber the clauses of her mind two to one. -/
def pratchett : Style where
  name := "pratchett"
  rules := [
    ("footnotes", .ratioAtLeast .footnotes .paras 1 2),
    ("footnotes anchored", .footnotesPaired),
    ("footnotes generalise", .footnotesGeneric),
    ("footnotes brief", .ratioAtMost .footnoteWords .words 1 5),
    ("generics", .ratioAtLeast .generics .sents 1 4),
    ("similes", .ratioAtLeast .likeSimiles .paras 1 2),
    ("Concepts", .ratioAtLeast .concepts .paras 1 2),
    ("asides over interiority", .ratioAtLeast .asides .interior 2 1)]

end LangLib.Style
