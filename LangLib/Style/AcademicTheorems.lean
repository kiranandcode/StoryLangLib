import LangLib.Style.Data.AcademicRoof
import LangLib.Style.Data.AcademicRoofPratchett

/-!
# The academic rules on the fiction

The roof story and the roof story told in Pratchett's manner, measured by the
academic-style features (records in `Data/Academic*.lean`), so their rhythm
and register can be compared with the papers' (`docs/style-academic.md`). The
papers' own records stay with their private texts.
-/

namespace LangLib.Style.Academic

def roofAF : AFeatures := AFeatures.ofSents roofASentsLore roofASents
def roofPratchettAF : AFeatures := AFeatures.ofSents roofPratchettASentsLore roofPratchettASents


/-- Fiction has no use for promises, so introductions wait longer than three
sentences; the story's annotation has no verb forms. -/
theorem roof_verdicts :
    kiran.failing roofAF = ["just in time"] ∧ llmismFree.failing roofAF = [] ∧
    annotated.failing roofAF = ["every verb has a form and finite ones a tense", "every colon and dash classified"] := by
  decide +kernel

theorem roof_pratchett_verdicts :
    kiran.failing roofPratchettAF = ["just in time", "motifs"] ∧ llmismFree.failing roofPratchettAF = [] := by
  decide +kernel

end LangLib.Style.Academic
