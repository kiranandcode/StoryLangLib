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

theorem roof_features : roofAF = { sents := 76, words := 946, paras := 9, multiParas := 9, firstSum := 8, tracked := 51, oldSubj := 48, newEnts := 24, newLate := 21, reused := 17, jit := 6, promisedIntro := 0, gap1 := 3, gap3 := 3, gap6 := 3, gapFar := 8, single := 17, callbacks := 10, motifs := 2, asks := 2, answered := 2, questions := 0, rhetorical := 0, colonsDef := 1, colonsDram := 0, dashesDef := 0, dashesDram := 0, unclassified := 1, negTurns := 2, antithesis := 0, bodySents := 70, lenSum := 933, lenSq := 17655, jumpSum := 570, jumpPairs := 61, punches := 0, longRuns := 0, longestRun := 2, formal := 1, informal := 13, technical := 6, neutral := 368, untagged := 0, untensed := 220 } := by decide +kernel
theorem roof_pratchett_features : roofPratchettAF = { sents := 59, words := 876, paras := 6, multiParas := 6, firstSum := 5, tracked := 38, oldSubj := 34, newEnts := 23, newLate := 19, reused := 13, jit := 5, promisedIntro := 0, gap1 := 3, gap3 := 2, gap6 := 3, gapFar := 5, single := 18, callbacks := 8, motifs := 0, asks := 1, answered := 1, questions := 0, rhetorical := 0, colonsDef := 2, colonsDram := 0, dashesDef := 0, dashesDram := 0, unclassified := 1, negTurns := 2, antithesis := 0, bodySents := 55, lenSum := 867, lenSq := 19099, jumpSum := 584, jumpPairs := 49, punches := 3, longRuns := 0, longestRun := 2, formal := 1, informal := 9, technical := 3, neutral := 365, untagged := 0, untensed := 196 } := by decide +kernel

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
