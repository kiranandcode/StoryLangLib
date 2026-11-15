import LangLib.Style.Pratchett
import LangLib.Style.Roof
import LangLib.Style.Data.Roof

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

end LangLib.Style
