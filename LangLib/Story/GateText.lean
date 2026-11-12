import LangLib.Json
import LangLib.Check
import LangLib.Story.Bridge
import LangLib.Story.GateScene

/-!
# The gate scene, from text

The passage in `examples/gate.txt`, annotated in `examples/gate.json`, passes
the faithfulness check; reading events off it gives exactly the setup of the
gate story plus Kiran's shout, which is a valid story.
-/

namespace LangLib.Scene.Gate
open LangLib LangLib.Scene Ch Pl Ob

def resolver : Resolver Ch Pl Ob where
  char | "kiran" => some .kiran | "mara" => some .mara | "guard" => some .guard | _ => none
  place | "gate" => some .gate | "cellar" => some .cellar | _ => none
  obj | "key" => some .key | _ => none

def passage : String := include_str "../../examples/gate.txt"
def annotated : String := include_str "../../examples/gate.json"

def fromText : List E := [.move mara cellar, .hide mara key, .move mara gate,
                          .grab .guard mara, .shout kiran .guard]

-- the encoding is faithful to the passage
#guard match docOfString annotated with
  | .ok d => (check passage d).ok | .error _ => false

-- and the events it asserts are these
#guard match docOfString annotated with
  | .ok d => (d.events resolver).map (·.2) == fromText | .error _ => false

theorem fromText_valid : Valid start fromText := validB_sound _ _ (by decide +kernel)

/-! Time: what the text lets us prove about when. -/

/-- After the first event ("Mara slipped into the cellar"), Mara is in the cellar. -/
theorem mara_in_cellar_at_1 : (start.at fromText 1).loc mara = cellar := by decide

/-- So Mara was, at some point, in the cellar ... -/
theorem mara_was_in_cellar : Was start fromText (fun s => s.loc mara = cellar) :=
  ⟨1, by decide, by decide⟩

/-- ... but by the end she is back at the gate. -/
theorem mara_at_gate_at_end : (start.at fromText fromText.length).loc mara = gate := by decide

/-- She saw where the key went: Mara knows it is in the cellar from time 2 on
(time `i + 2` for every `i` up to the end). -/
theorem mara_knows_key_from_2 :
    ∀ i, i ≤ fromText.length - 2 → (Fact.objAt key cellar) ∈ (start.at fromText (i + 2)).knows mara := by
  decide

/-- Kiran never left the gate, so she never learned it: the leak variant is a plot hole. -/
theorem kiran_never_knows_key :
    Throughout start fromText (fun s => Fact.objAt key cellar ∉ s.knows kiran) := by
  unfold Throughout; decide

end LangLib.Scene.Gate
