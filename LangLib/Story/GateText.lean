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

end LangLib.Scene.Gate
