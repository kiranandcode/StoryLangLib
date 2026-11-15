import LangLib.Style.Core

namespace LangLib.Style

/-- Roof's style: close third person, interiority over choreography.

* close third: most clauses with a character for subject are the
  point-of-view character's, and no narrator stands outside her (no footnotes,
  no generalisations, no parentheticals);
* interiority: her mind (verbs of perceiving, thinking, wanting; states she is
  in; what she tells herself) outweighs any narrator aside;
* the scene is carried in talk with plain tags ("said"), no capitalised Concepts. -/
def roofStyle : Style where
  name := "roof"
  rules := [
    ("close third", .ratioAtLeast .povClauses .charClauses 1 2),
    ("no footnotes", .atMost .footnotes 0),
    ("no parentheticals", .atMost .prn 0),
    ("few generalisations", .ratioAtMost .generics .sents 1 20),
    ("interiority over asides", .ratioAtLeast .interior .asides 3 1),
    ("no Concepts", .atMost .concepts 0),
    ("dialogue", .ratioAtLeast .quoteWords .words 1 10),
    ("plain tags", .ratioAtMost .fancyTags .tags 1 3)]

end LangLib.Style
