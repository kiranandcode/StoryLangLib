import LangLib.Style.Pratchett
import LangLib.Style.Roof
import LangLib.Style.Data.Roof
import LangLib.Style.Data.RoofPratchett

/-!
# Which story is in which style

The per-sentence records in `Data/` are printed by `langlib style <dir> --lean`
from the checked annotations, by the same `sentOf` the report uses; the
features and the verdicts below are recomputed from them by the kernel.
-/

namespace LangLib.Style

def roofFeatures : Features := Features.ofSents roofSents

/-- Roof is in its own style: close third, interiority over asides. -/
theorem roof_roof : roofStyle.holds roofFeatures = true := by decide +kernel

/-- Roof is not Pratchett: no footnotes, no generalisations, no "like" similes,
no Concepts, and no narrator asides to outweigh her mind. -/
theorem roof_not_pratchett :
    pratchett.failing roofFeatures =
      ["footnotes", "generics", "similes", "Concepts", "asides over interiority"] := by
  decide +kernel

/-- Read literally, roof's own description fails: 11 clauses of her mind against
79 of choreography. Its interiority is in free indirect lines and evaluation,
which no verb class sees; the style is stated as interiority over asides. -/
theorem roof_not_literally_interiority_over_choreography :
    (Rule.ratioAtLeast .interior .choreo 1 1).holds roofFeatures = false := by decide +kernel

def roofPratchettFeatures : Features := Features.ofSents roofPratchettSents

/-- The Pratchett telling is in Pratchett's manner: every rule holds. -/
theorem roofPratchett_pratchett : pratchett.holds roofPratchettFeatures = true := by decide +kernel

/-- ...and not in roof's: the narrator footnotes, generalises, outweighs her
mind and capitalises Concepts. -/
theorem roofPratchett_not_roof :
    roofStyle.failing roofPratchettFeatures =
      ["no footnotes", "few generalisations", "interiority over asides", "no Concepts"] := by
  decide +kernel

end LangLib.Style
