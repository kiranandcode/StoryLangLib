import LangLib
import LangLib.Studio.PaperArg
import LangLib.Studio.RulesView
import LangLib.World.Examples.FightPower
open LangLib LangLib.Scene Lean

def usage : String := "usage:
  langlib tokenize <text-file>              print tokens, one per line
  langlib check <text-file> <doc.json>      check an encoding against its text (JSON report)
  langlib render <doc.json>                 print the text a document renders to
  langlib pretty <doc.json>                 print bracketed trees
  langlib story <dir>                       check a story directory, per paragraph (JSON report)
  langlib story-lean <dir> <namespace>      print the story as a Lean file of theorems
  langlib style <dir> [--pov id] [--lean name]  style features and verdicts (or the records as Lean)
  langlib academic <dir> [--lean name]      academic-style flow features and verdicts (or the records as Lean)
  langlib house <dir> [--lean name]         house style (/writelikeme) and clarity verdicts, flagged sentences
  langlib consent <dir> [--lean ns]         the refined consent reading (World/Consent), or it as Lean theorems
  langlib ext <dir> [--lean ns]             ties, care and identity (World/Ties, Care, Identity), or as Lean theorems
  langlib end <dir>                         the end state of every reading, as the next chapter's opening (JSON)
  langlib chain-lean <prev> <next> <ns>     the link between two chapters as Lean theorems (Chain.lean)
  langlib argument <dir> <lore-json>        a paper's argument graph (World/Argument) with its grounded labelling
  langlib rules <dir>                       the argument's inferences as rules (World/Rules): schemes, attacks, labels
  langlib rules-json <file>                 check a rules document built elsewhere (a story adapter) with World/Rules
  langlib power <dir>                       a rule-based module's moves, checks and states (studio/power-schema.md)"

def readDoc (p : String) : IO Doc := do
  match docOfString (← IO.FS.readFile p) with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"parse error: {e}")

/-- The Power exports, by story directory (studio/power-schema.md): one line per module. -/
def powerExports : List (String × (Unit → Json)) :=
  [("hxh-chrollo-hisoka", fun _ => LangLib.World.Fight.powerExport.toJson)]

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
  | "style" :: dir :: opts => do
    IO.println (← LangLib.Style.styleMain dir opts)
    pure 0
  | "house" :: dir :: opts => do
    IO.println (← LangLib.Style.House.houseMain dir opts)
    pure 0
  | "academic" :: dir :: opts => do
    IO.println (← LangLib.Style.Academic.academicMain dir opts)
    pure 0
  | ["consent", dir] => do
    IO.println (← LangLib.Studio.consentReport dir).compress
    pure 0
  | ["consent", dir, "--lean", ns] => do
    IO.print (← LangLib.Studio.consentLean dir ns)
    pure 0
  | ["ext", dir] => do
    IO.println (← LangLib.Studio.extReport dir).compress
    pure 0
  | ["ext", dir, "--lean", ns] => do
    IO.print (← LangLib.Studio.extLean dir ns)
    pure 0
  | ["chain-lean", prev, next, ns] => do
    IO.print (← LangLib.Studio.chainLean prev next ns)
    pure 0
  | ["end", dir] => do
    IO.println (← LangLib.Studio.endReport dir).pretty
    pure 0
  | ["argument", dir, lore] => do
    IO.println (← LangLib.Studio.PaperArg.argumentMain dir lore).compress
    pure 0
  | ["rules", dir] => do
    IO.println (← LangLib.Studio.RulesView.rulesMain dir).compress
    pure 0
  | ["rules-json", file] => do
    IO.println (← LangLib.Studio.RulesView.rulesJsonMain file).compress
    pure 0
  | ["power", dir] => do
    let name := ((System.FilePath.mk dir).fileName.getD dir)
    match powerExports.find? (·.1 == name) with
    | some (_, f) => IO.println (f ()).compress; pure 0
    | none => IO.println (Json.mkObj [("error", s!"no power export for {name}"),
        ("available", toJson (powerExports.map (·.1)))]).compress; pure 1
  | _ => do IO.eprintln usage; pure 64
