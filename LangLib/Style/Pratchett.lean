import LangLib.Style.Core

namespace LangLib.Style

/-- Terry Pratchett's manner, as far as trees show it (placeholder thresholds). -/
def pratchett : Style where
  name := "pratchett"
  rules := [
    ("footnotes", .ratioAtLeast .footnotes .paras 1 3),
    ("footnotes anchored", .footnotesPaired),
    ("footnotes generalise", .footnotesGeneric),
    ("generics", .ratioAtLeast .generics .sents 1 6),
    ("similes", .ratioAtLeast .likeSimiles .paras 1 3),
    ("Concepts", .atLeast .concepts 2),
    ("asides over interiority", .ratioAtLeast .asides .interior 1 1)]

end LangLib.Style
