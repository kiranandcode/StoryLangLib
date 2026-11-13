import LangLib.World.Goals

/-!
# Escape hatch for unusual instances

Story event and fact types are declared as named inductives that derive their
instances (`deriving StoryEvent`, `deriving StoryFact`; see `Derive.lean`), so
instance search neither backtracks nor builds large terms. For anything else
that would exceed `synthInstance.maxSize`, `cached_instance C` declares the
instance once at top level, so later searches use it as a single atom.
-/

namespace LangLib.World

open Lean in
/-- `cached_instance C` declares one composite instance, e.g.
`cached_instance DecidableEq A` for a story's action type. -/
macro "cached_instance " t:term : command => do
  let o := mkIdent `synthInstance.maxSize
  `(set_option $o 2048 in instance : $t := inferInstance)

end LangLib.World

