import LangLib.Style.Data.AcademicRoof
import LangLib.Style.Data.AcademicRoofPratchett

/-!
# The academic and house rules on the fiction

The roof story and the roof story told in Pratchett's manner, measured by the
academic-style features and by the house style (`/writelikeme` and the clarity
check), so they can be compared with the papers (`docs/style-academic.md`).
The papers' own records stay with their private texts.
-/

namespace LangLib.Style.House
open LangLib.Style.Academic

def roofAF : AFeatures := AFeatures.ofSents roofASentsLore roofASents
def roofHF : HFeatures := HFeatures.ofSents roofASentsLore roofASents roofASentsH

theorem roof_academic : roofAF = { words := 946, unusedIntro := 34, untensed := 220, untagged := 0, unreadReasons := 4, unreadHedges := 0, unreadDenials := 2, ungroundedReasons := 0, ungroundedHedges := 0, ungroundedDenials := 0, unclassified := 1, tracked := 51, technical := 6, single := 17, shortClosers := 1, sents := 76, rhetorical := 0, reused := 17, questions := 0, punches := 0, promisedIntro := 0, paras := 9, oldSubj := 48, newLate := 21, newEnts := 24, neutral := 368, negTurns := 2, neededIntro := 0, multiParas := 9, motifs := 2, longestRun := 2, longRuns := 0, lenSum := 933, lenSq := 17655, jumpSum := 570, jumpPairs := 61, jit := 6, informal := 13, hedgedSents := 0, gapFar := 8, gap6 := 3, gap3 := 3, gap1 := 3, frontings := 7, formal := 1, firstSum := 8, deliberate := 1, dashesDram := 0, dashesDef := 0, colonsDram := 0, colonsDef := 1, callbacks := 10, bridged := 0, bodySents := 70, asks := 2, antithesis := 0, answered := 2, announced := 0 } := by decide +kernel
theorem roof_house : roofHF = { usSpelling := 0, tricolons := 0, trailingCadence := 0, throat := 0, tetracola := 0, summaryClosers := 4, summarisingPivots := 0, stacked := 0, spuriousContrasts := 0, slopEmphasis := 0, sents := 76, pseudoClefts := 0, passives := 0, nounStacks := 0, nonSequiturs := 30, itClefts := 0, intensifiers := 2, initialConj := 0, inflation := 0, inanimate := 2, hiddenAction := 0, dramaticTerminal := 0, clauses := 172, buzz := 0, buried := 0, bareRelatives := 2, barePivots := 0, bareAsides := 0, andJoins := 11, agentless := 0, negDashes := 0, abstractSig := 0 } := by decide +kernel
theorem roof_verdicts :
    kiran.failing roofAF = ["just in time"] ∧ llmismFree.failing roofAF = [] ∧
    clarity.failing roofHF = ["no inanimate actors", "no non-sequitur stacks"] ∧ writeLikeMe.failing roofHF = ["few observation-and-response joins", "no empty intensifiers", "no summary closers", "no bare relative clauses"] := by
  decide +kernel

def roofPratchettAF : AFeatures := AFeatures.ofSents roofPratchettASentsLore roofPratchettASents
def roofPratchettHF : HFeatures := HFeatures.ofSents roofPratchettASentsLore roofPratchettASents roofPratchettASentsH

theorem roofPratchett_academic : roofPratchettAF = { words := 876, unusedIntro := 31, untensed := 196, untagged := 0, unreadReasons := 3, unreadHedges := 0, unreadDenials := 2, ungroundedReasons := 0, ungroundedHedges := 0, ungroundedDenials := 0, unclassified := 1, tracked := 38, technical := 3, single := 18, shortClosers := 0, sents := 59, rhetorical := 0, reused := 13, questions := 0, punches := 3, promisedIntro := 0, paras := 6, oldSubj := 34, newLate := 19, newEnts := 23, neutral := 365, negTurns := 2, neededIntro := 0, multiParas := 6, motifs := 0, longestRun := 2, longRuns := 0, lenSum := 867, lenSq := 19099, jumpSum := 584, jumpPairs := 49, jit := 5, informal := 9, hedgedSents := 0, gapFar := 5, gap6 := 3, gap3 := 2, gap1 := 3, frontings := 6, formal := 1, firstSum := 5, deliberate := 0, dashesDram := 0, dashesDef := 0, colonsDram := 0, colonsDef := 2, callbacks := 8, bridged := 0, bodySents := 55, asks := 1, antithesis := 0, answered := 1, announced := 0 } := by decide +kernel
theorem roofPratchett_house : roofPratchettHF = { usSpelling := 0, tricolons := 0, trailingCadence := 0, throat := 0, tetracola := 0, summaryClosers := 0, summarisingPivots := 0, stacked := 0, spuriousContrasts := 0, slopEmphasis := 0, sents := 59, pseudoClefts := 0, passives := 0, nounStacks := 0, nonSequiturs := 24, itClefts := 0, intensifiers := 0, initialConj := 0, inflation := 0, inanimate := 1, hiddenAction := 0, dramaticTerminal := 0, clauses := 149, buzz := 0, buried := 0, bareRelatives := 2, barePivots := 0, bareAsides := 0, andJoins := 8, agentless := 0, negDashes := 0, abstractSig := 0 } := by decide +kernel
theorem roofPratchett_verdicts :
    kiran.failing roofPratchettAF = ["just in time", "motifs"] ∧ llmismFree.failing roofPratchettAF = [] ∧
    clarity.failing roofPratchettHF = ["no inanimate actors", "no non-sequitur stacks"] ∧ writeLikeMe.failing roofPratchettHF = ["few observation-and-response joins", "no bare relative clauses"] := by
  decide +kernel

end LangLib.Style.House
