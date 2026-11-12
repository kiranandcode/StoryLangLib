import LangLib
open LangLib Lean

def usage : String := "usage:
  langlib tokenize <text-file>              print tokens, one per line
  langlib check <text-file> <doc.json>      check an encoding against its text (JSON report)
  langlib render <doc.json>                 print the text a document renders to
  langlib pretty <doc.json>                 print bracketed trees"

def readDoc (p : String) : IO Doc := do
  match docOfString (← IO.FS.readFile p) with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"parse error: {e}")

def main : List String → IO UInt32
  | ["tokenize", f] => do
    for t in tokenize (← IO.FS.readFile f) do IO.println t
    pure 0
  | ["check", tf, df] => do
    let text ← IO.FS.readFile tf
    match docOfString (← IO.FS.readFile df) with
    | .error e =>
      IO.println (Json.mkObj [("ok", false), ("parseError", e)]).compress
      pure 2
    | .ok d =>
      let r := check text d
      IO.println (r.toJson text).pretty
      pure (if r.ok then 0 else 1)
  | ["render", df] => do IO.println (← readDoc df).toText; pure 0
  | ["pretty", df] => do
    for s in (← readDoc df).sentences do IO.println s.tree.pretty
    pure 0
  | _ => do IO.eprintln usage; pure 64
