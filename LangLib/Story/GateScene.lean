import LangLib.Story.Scene

/-!
# Example: the gate

Kiran is timid and ranks loyalty above safety above pride; Mara is her friend.
Mara slips into the cellar and hides the key while Kiran waits at the gate.
A guard grabs Mara; Kiran shouts at him. Mara then tells Kiran where the key is,
and Kiran fetches it.

Variants:
* `leak`: Kiran tells the guard where the key is, though she never saw it
  hidden and nobody told her: a plot hole (hard precondition fails).
* `unprovoked`: Kiran shouts at the guard with no threat to Mara: out of
  character (her timidity is defeasibly provable and nothing overrides it).
* `tipsy`: Kiran has been drinking; the shout is in character (drink blocks
  the timidity default) but unmotivated.
* `gagged`: the guard gags Kiran first; she cannot shout at all.
-/

namespace LangLib.Scene.Gate
open LangLib.DL LangLib.Scene

inductive Ch | kiran | mara | guard deriving DecidableEq, Repr
inductive Pl | gate | cellar deriving DecidableEq, Repr
inductive Ob | key deriving DecidableEq, Repr
open Ch Pl Ob

def persona : Ch → Persona Ch
  | kiran => { traits := [.timid], values := [.loyalty, .safety, .pride], allies := [mara] }
  | mara => { traits := [.brash], values := [.pride, .loyalty, .safety], allies := [kiran] }
  | .guard => { traits := [], values := [.safety], allies := [] }

def start : State Ch Pl Ob :=
  { persona, loc := fun _ => gate, holder := fun _ => some mara, objLoc := fun _ => gate }

abbrev E := Event Ch Pl Ob

def setup : List E :=
  [.move mara cellar, .hide mara key, .move mara gate, .grab guard mara]

def story : List E :=
  setup ++ [.shout kiran guard, .tell mara kiran (.objAt key cellar),
            .move kiran cellar, .take kiran key]

def leak : List E :=
  setup ++ [.shout kiran guard, .tell kiran guard (.objAt key cellar)]

def unprovoked : List E := [.shout kiran guard]

def tipsy : List E := [.drink kiran, .shout kiran guard]

def gagged : List E := [.gag guard kiran, .shout kiran guard]

/-- The main story is valid; the proof is a checked defeasible-logic certificate. -/
theorem story_valid : Valid start story := validB_sound _ _ (by decide +kernel)

theorem tipsy_valid : Valid start tipsy := validB_sound _ _ (by decide +kernel)

/-- After the setup, Kiran's shout is not just allowed but motivated: protecting
Mara (loyalty) overrides her timidity (safety). -/
theorem shout_motivated : Motivated (start.step (.move mara cellar) |>.step (.hide mara key)
    |>.step (.move mara gate) |>.step (.grab guard mara)) kiran guard := by
  let s := start.step (.move mara cellar) |>.step (.hide mara key)
    |>.step (.move mara gate) |>.step (.grab guard mara)
  have h := Cert.sound (shoutTheory s kiran guard) (certify (shoutTheory s kiran guard)) (by decide +kernel)
  exact h.1 _ (by decide +kernel)

/-- Telling what you never learned is a plot hole. -/
theorem leak_invalid : ¬ Valid start leak := by
  intro h
  simp only [leak, setup, List.cons_append, List.nil_append] at h
  cases h with | cons _ _ h =>
  cases h with | cons _ _ h =>
  cases h with | cons _ _ h =>
  cases h with | cons _ _ h =>
  cases h with | cons _ _ h =>
  cases h with | cons hpre _ _ =>
  revert hpre; decide +kernel

/-- An unprovoked shout is out of character: Kiran's timidity is defeasibly
provable, and by coherence its negation cannot be refuted. -/
theorem unprovoked_invalid : ¬ Valid start unprovoked := by
  intro h
  cases h with | cons _ hc _ =>
  have h := Cert.sound (shoutTheory start kiran guard) (certify (shoutTheory start kiran guard))
    (by decide +kernel)
  exact not_inCharacter_of_def start kiran guard (h.1 _ (by decide +kernel)) hc

theorem gagged_invalid : ¬ Valid start gagged := by
  intro h
  cases h with | cons _ _ h =>
  cases h with | cons hpre _ _ =>
  revert hpre; decide +kernel

instance : ToString Ch := ⟨fun | .kiran => "Kiran" | .mara => "Mara" | .guard => "the guard"⟩
instance : ToString Pl := ⟨fun | .gate => "gate" | .cellar => "cellar"⟩
instance : ToString Ob := ⟨fun | .key => "key"⟩

def report (name : String) (es : List E) : IO Unit := do
  IO.println s!"── {name}"
  for l in explain start es do IO.println l

#eval do
  report "story" story; report "leak" leak; report "unprovoked" unprovoked
  report "tipsy" tipsy; report "gagged" gagged

end LangLib.Scene.Gate
