import Lean.Data.Json
import LangLib.Json
import LangLib.Style.Pratchett
import LangLib.Style.Roof
import LangLib.Style.Ao3

/-!
# `langlib style <dir>`

Reads `<dir>/paragraphs/NN.json` in order, with the point-of-view character
from `<dir>/story.json` (`"pov"`, or `--pov id`) and the cast from its
`"characters"`, and reports the story's style features and each known style's
verdict. `--lean <name>` prints the per-sentence records instead, as a Lean
definition a theorem file can restate (`Theorems.lean`).
-/

namespace LangLib.Style
open Lean LangLib

def knownStyles : List Style := [pratchett, roofStyle, ao3, roofRan]

/-- A paragraph annotation file: `NN.json`, two digits. -/
def isParaDoc (n : String) : Bool :=
  n.length == 7 && n.endsWith ".json" && (n.toList.take 2).all Char.isDigit

def loadSents (dir : String) (pov? : Option String) : IO (List Sent × Ctx) := do
  let story ← match Json.parse (← IO.FS.readFile s!"{dir}/story.json") with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"story.json: {e}")
  let pov := pov?.getD ((story.getObjValAs? String "pov").toOption.getD "")
  let chars := match story.getObjVal? "characters" with
    | .ok (.arr a) => a.toList.filterMap fun c => (c.getObjValAs? String "id").toOption
    | _ => []
  let paper := (story.getObjValAs? String "kind").toOption == some "paper"
  let cx : Ctx := { pov, chars, paper }
  let names := ((← System.FilePath.readDir s!"{dir}/paragraphs").map (·.fileName)).toList.filter isParaDoc
  let names := names.mergeSort (· ≤ ·)
  let mut out : List Sent := []
  for n in names do
    let para := (String.ofList (n.toList.take 2)).toNat!
    match docOfString (← IO.FS.readFile s!"{dir}/paragraphs/{n}") with
    | .ok d => out := out ++ sentsOfDoc cx para d
    | .error e => throw (IO.userError s!"{n}: {e}")
  pure (out, cx)

def Features.toJson (f : Features) : Json :=
  Json.mkObj ((Feat.all.map fun x => (x.name, Lean.toJson (f.get x))) ++
    [("footPaired", Lean.toJson f.footPaired), ("footGeneric", Lean.toJson f.footGeneric)])

def report (ss : List Sent) (cx : Ctx) : Json :=
  let f := Features.ofSents ss
  Json.mkObj [
    ("pov", cx.pov),
    ("features", f.toJson),
    ("styles", Json.arr (knownStyles.map fun st =>
      Json.mkObj [("name", st.name), ("holds", st.holds f),
        ("failing", Json.arr ((st.failing f).map (fun n => Json.str n)).toArray),
        ("rules", Json.arr (st.rules.map fun (n, r) =>
          Json.mkObj [("name", n), ("rule", r.show), ("holds", r.holds f)]).toArray)]).toArray)]

/-- The per-sentence records as a Lean definition. -/
def leanDef (name : String) (ss : List Sent) : String :=
  let body := ",\n   ".intercalate (ss.map fun s => (Std.Format.pretty (repr s) 1000))
  s!"def {name} : List Sent :=\n  [{body}]\n"

def styleMain (dir : String) (opts : List String) : IO String := do
  let rec opt : List String → String → Option String
    | k :: v :: rest, key => if k == key then some v else opt (v :: rest) key
    | _, _ => none
  let (ss, cx) ← loadSents dir (opt opts "--pov")
  match opt opts "--lean" with
  | some name => pure (leanDef name ss)
  | none => pure (report ss cx).pretty

end LangLib.Style
