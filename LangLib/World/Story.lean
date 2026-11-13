import LangLib.World.Goals

/-!
# Declaring a story world

Instance synthesis is limited by the *size* of the term it builds
(`synthInstance.maxSize`, default 128). A story's event type is a sum of
modules, and each module's `Domain` instance takes a dozen instance arguments,
some of them sums again (truth over the story's fact type), so the composite
term for a four-module story exceeds the limit.

The remedy (Lean reference manual, *Instance Synthesis*: keep instance terms
small) is to declare the composite instances once, at top level: a declared
instance is a single atom in later searches. `world_instances W, E, Φ, P, C`
does that for a story with world `W`, events `E`, facts `Φ`, places `P` and
characters `C`.
-/

namespace LangLib.World

open Lean in
/-- Declare the composite instances of a story world once, so that later
synthesis uses them as atoms. (The size limit is raised only while building
these; the option name is built with `mkIdent` so macro hygiene leaves it alone.) -/
macro "world_instances " W:term ", " E:term ", " Φ:term ", " P:term ", " C:term : command => do
  let o := mkIdent `synthInstance.maxSize
  `(set_option $o 2048 in instance : DecidableEq $E := inferInstance
    set_option $o 2048 in instance : Truth $W $Φ := inferInstance
    set_option $o 2048 in instance : Supersedes $Φ := inferInstance
    set_option $o 2048 in instance : Fluent $Φ := inferInstance
    set_option $o 2048 in instance : Observable $W $E $Φ $P := inferInstance
    set_option $o 2048 in instance : Purpose $W $E $C $Φ := inferInstance
    set_option $o 2048 in instance : Domain $W $E := inferInstance
    set_option $o 2048 in instance : Perceive $W $E := inferInstance)

open Lean in
/-- `cached_instance C` declares one composite instance, e.g.
`cached_instance DecidableEq A` for a story's action type. -/
macro "cached_instance " t:term : command => do
  let o := mkIdent `synthInstance.maxSize
  `(set_option $o 2048 in instance : $t := inferInstance)

end LangLib.World
