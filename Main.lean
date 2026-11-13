import LangLib
open LangLib LangLib.Scene Lean

def usage : String := "usage:
  langlib tokenize <text-file>              print tokens, one per line
  langlib check <text-file> <doc.json>      check an encoding against its text (JSON report)
  langlib render <doc.json>                 print the text a document renders to
  langlib pretty <doc.json>                 print bracketed trees
  langlib story <dir>                       check a story directory, per paragraph (JSON report)
  langlib story-lean <dir> <namespace>      print the story as a Lean file of theorems"

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
  | ["gate-events", df] => do
    -- clauses and the gate-scene events they assert (for the bridge diagram)
    let d ← readDoc df
    let toks := d.render
    let out := (d.clauses).map fun c =>
      Json.mkObj [("verb", c.verb), ("at", c.at_), ("word", toks.getD c.at_ ""),
        ("subj", c.subj.getD ""), ("obj", c.obj.getD ""),
        ("obls", Json.arr (c.obls.map fun (p, e) => Json.arr #[p, e]).toArray),
        ("event", match c.event LangLib.Scene.Gate.resolver with
          | some e => reprStr e | none => "")]
    IO.println (Json.arr out.toArray).pretty
    pure 0
  | ["clauses", df] => do
    let d ← readDoc df
    let toks := d.render
    for c in d.clauses do
      IO.println s!"{toks.getD c.at_ ""}/{c.verb} subj={c.subj} obj={c.obj} objNoun={c.objNoun} obls={c.obls} oblNouns={c.oblNouns} comp={c.comp.map (toks.getD · "")} embedded={c.embedded} advs={c.advs}"
    pure 0
  | ["story", dir] => do
    try
      IO.println (← LangLib.Studio.storyReport dir).compress
      pure 0
    catch e =>
      IO.println (Json.mkObj [("error", toString e)]).compress
      pure 1
  | ["story-lean", dir, ns] => do
    IO.print (← LangLib.Studio.storyLean dir ns)
    pure 0
  | _ => do IO.eprintln usage; pure 64
