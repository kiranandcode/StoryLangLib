import LangLib.Style.Ao3
import LangLib.Style.Roof
import LangLib.Style.Data.Ao3Boyremoval
import LangLib.Style.Data.Ao3SweetGirl

/-!
# The AO3 style, checked on the two chapters it was measured on

The records in `Data/` are printed by `langlib style <dir> --lean` from the
chapters' checked annotations (counts only; the texts stay private).
-/

namespace LangLib.Style

def ao3BoyremovalFeatures : Features := Features.ofSents ao3BoyremovalSents
def ao3SweetGirlFeatures : Features := Features.ofSents ao3SweetGirlSents

/-- Both chapters are in the shared AO3 style. -/
theorem boyremoval_ao3 : ao3.holds ao3BoyremovalFeatures = true := by decide +kernel
theorem sweetGirl_ao3 : ao3.holds ao3SweetGirlFeatures = true := by decide +kernel

/-- What they do not share, and so the style leaves out: one is told in the
first person, the other is not; one breaks narration into fragments, the other
never does. -/
theorem ao3_person_differs :
    ao3BoyremovalFeatures.firstPerson > 0 ∧ ao3SweetGirlFeatures.firstPerson = 0 := by decide +kernel
theorem ao3_fragments_differ :
    ao3BoyremovalFeatures.frags = 0 ∧ ao3SweetGirlFeatures.frags > 0 := by decide +kernel

/-- Talk through the chapter: it falls in the second half of one and rises in
the other, so "dialogue rises as the scene escalates" is not a shared rule. -/
theorem ao3_talk_direction_differs :
    (Rule.crossAtLeast .quoteLate .wordsLate .quoteEarly .wordsEarly).holds ao3BoyremovalFeatures = false ∧
    (Rule.crossAtLeast .quoteLate .wordsLate .quoteEarly .wordsEarly).holds ao3SweetGirlFeatures = true := by
  decide +kernel

end LangLib.Style
