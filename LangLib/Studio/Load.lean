import LangLib.Studio.Report

/-!
# Story directories

```
stories/<name>/
  story.json                 the world (see `Parse.lean`), beats, fact lexicon
  paragraphs/NN.txt          the prose of paragraph NN
  paragraphs/NN.plan.json    {"beat": "...", "events": [...], "claims": [...]}
  paragraphs/NN.json         its langlib annotation
  paragraphs/NN.events.json  {"events": [{"e": "...", "at": 12, "phase": "main"}], "claims": [...]}
```

A paragraph's events are those read off its prose (`events.json`) when there
are any, else its plan. `storyLean` writes the story as a Lean file whose
theorems are the report's verdicts, proved by `decide`.
-/

namespace LangLib.Studio
open Lean LangLib LangLib.World

structure Loaded where
  spec : Spec
  beats : Option Beats
  beatStory : List String
  lex : List FactLex
  paras : List Para

private def readJson (p : System.FilePath) : IO (Option Json) := do
  if !(← p.pathExists) then return none
  match Json.parse (← IO.FS.readFile p) with
  | .ok j => return some j
  | .error e => throw (IO.userError s!"{p}: {e}")

private def strs (j : Json) (k : String) : List String :=
  ((j.getObjValAs? (Array String) k).toOption.getD #[]).toList

private def arr (j : Json) (k : String) : List Json :=
  match j.getObjVal? k with | .ok (.arr a) => a.toList | _ => []

def beatsOfJson (n : Names) (j : Json) : Except String (Beats × List String) := do
  let conds := strs j "conds"
  let ci (c : String) : Except String Nat :=
    match conds.idxOf? c with | some i => pure i | none => throw s!"unknown beat condition \"{c}\""
  let vocab ← (arr j "vocab").mapM fun b => do
    let some id := (b.getObjValAs? String "id").toOption | throw "beat needs an id"
    pure ({ id, label := (b.getObjValAs? String "label").toOption.getD "",
            pre := ← (strs b "pre").mapM ci, add := ← (strs b "add").mapM ci,
            del := ← (strs b "del").mapM ci, keys := ← (strs b "keys").mapM n.ev } : Beat)
  pure ({ conds, vocab, init := ← (strs j "init").mapM ci }, strs j "story")

def loadStory (dir : System.FilePath) : IO Loaded := do
  let some sj ← readJson (dir / "story.json") | throw (IO.userError s!"no story.json in {dir}")
  let spec ← IO.ofExcept (specOfJson sj)
  let n := spec.names
  let (beats, beatStory) ← match sj.getObjVal? "beats" with
    | .ok bj => do let (b, st) ← IO.ofExcept (beatsOfJson n bj); pure (some b, st)
    | .error _ => pure (none, [])
  let lex ← (arr sj "lexicon").mapM fun l => do
    let some verb := (l.getObjValAs? String "verb").toOption | throw (IO.userError "lexicon entry needs a verb")
    let some li := (l.getObjValAs? String "lit").toOption | throw (IO.userError "lexicon entry needs a lit")
    pure ({ verb, subj := (l.getObjValAs? String "subj").toOption, obj := (l.getObjValAs? String "obj").toOption,
            lit := ← IO.ofExcept (n.lit li) } : FactLex)
  let pdir := dir / "paragraphs"
  let names ← if ← pdir.pathExists then do
      let es ← pdir.readDir
      pure ((es.toList.filterMap fun e =>
        let f := e.fileName
        if f.endsWith ".txt" || f.endsWith ".plan.json" then some ((f.splitOn ".").head!) else none).eraseDups.mergeSort (· ≤ ·))
    else pure []
  let paras ← names.mapM fun nm => do
    let txtP := pdir / s!"{nm}.txt"
    let text ← if ← txtP.pathExists then IO.FS.readFile txtP else pure ""
    let mut errors : List String := []
    let doc ← match ← readJson (pdir / s!"{nm}.json") with
      | some j => match docOfJson j with
        | .ok d => pure (some d)
        | .error e => errors := errors ++ [s!"annotation: {e}"]; pure none
      | none => pure none
    let planJ ← readJson (pdir / s!"{nm}.plan.json")
    let evJ ← readJson (pdir / s!"{nm}.events.json")
    let mut plan : Option (List Ev) := none
    if let some pj := planJ then
      let mut ps := []
      for e in strs pj "events" do
        match n.ev e with
        | .ok ev => ps := ps ++ [ev]
        | .error m => errors := errors ++ [s!"plan: {m}"]
      plan := some ps
    let mut items : List Item := []
    if let some ej := evJ then
      for it in arr ej "events" do
        let some e := (it.getObjValAs? String "e").toOption | errors := errors ++ ["event without e"]
        match n.ev e with
        | .ok ev =>
          let src := (it.getObjValAs? String "src").toOption.getD "text"
          let at_ := (it.getObjValAs? Nat "at").toOption
          let phase := Phase.ofString ((it.getObjValAs? String "phase").toOption.getD "main")
          let gap := (it.getObjValAs? Nat "gap").toOption
          let item : Item := Item.mk ev src at_ phase gap
          items := items ++ [item]
        | .error m => errors := errors ++ [s!"events: {m}"]
    else if let some pj := planJ then
      -- plan items keep their phase annotations, if any
      let phases := arr pj "phases"
      items := (plan.getD []).zipIdx.map fun ((ev : Ev), (i : Nat)) =>
        let ph := (phases[i]?.bind fun (j : Json) => j.getStr?.toOption).getD "main"
        ({ ev := ev, src := "plan", phase := Phase.ofString ph } : Item)
    let claims := (evJ.map (strs · "claims")).getD [] ++ (planJ.map (strs · "claims")).getD []
    let beat := planJ.bind fun pj => (pj.getObjValAs? String "beat").toOption
    pure ({ name := nm, text, doc, plan, items, claims := claims.eraseDups, beat, errors } : Para)
  pure { spec, beats, beatStory, lex, paras }

def storyReport (dir : System.FilePath) : IO Json := do
  let l ← loadStory dir
  pure (report l.spec l.beats l.beatStory l.lex l.paras)

/-! ## The story as a Lean file -/

/-- The story file still says `s`. -/
def specMatches (str : String) (s : Spec) : Bool :=
  match Json.parse str >>= specOfJson with
  | .ok s' => s' == s
  | .error _ => false

/-- A paragraph's events file (or plan) still lists `evs`. -/
def eventsMatch (s : Spec) (str : String) (evs : List Ev) : Bool :=
  match Json.parse str with
  | .ok j =>
    let es := match j.getObjVal? "events" with
      | .ok (.arr a) => a.toList.filterMap fun (e : Json) =>
        (e.getStr?.toOption <|> (e.getObjValAs? String "e").toOption)
      | _ => []
    (es.mapM s.names.ev).toOption == some evs
  | .error _ => false

private def lean (s : String) : String :=
  -- `reprStr` output is Lean syntax; drop the namespaces we open
  ((s.replace "LangLib.Studio." "").replace "LangLib.World." "")

def storyLean (dir : System.FilePath) (ns : String) : IO String := do
  let l ← loadStory dir
  let s := l.spec
  let n := s.names
  let (story, owner) := storyOf (s := s) l.paras
  let some timed := story.solved
    | throw (IO.userError "the story's time constraints have no solution")
  let owner := owner.map (·.2)
  let mut out := s!"import LangLib.Studio\n\n/-!\n# {dir}: generated by `langlib story-lean`\n\n" ++
    "Every theorem here restates a verdict of the Studio's report and is proved by\n" ++
    "`decide +kernel`. Regenerate after editing the story; the `#guard` lines fail if\n" ++
    "the story files no longer match the definitions below.\n-/\n\n" ++
    s!"namespace {ns}\nopen LangLib.World LangLib.Studio\n\n"
  out := out ++ s!"def spec : Spec := {lean (reprStr s)}\n\n"
  out := out ++ "#guard specMatches (include_str \"story.json\") spec\n\n"
  let paraEvs := l.paras.map fun p => p.items.map (·.ev)
  for (p, evs) in l.paras.zip paraEvs do
    out := out ++ s!"/-- paragraph {p.name} -/\ndef p{p.name} : List Ev := {lean (reprStr evs)}\n"
    let src := if p.items.any (·.src != "plan") then s!"paragraphs/{p.name}.events.json" else s!"paragraphs/{p.name}.plan.json"
    out := out ++ s!"#guard eventsMatch spec (include_str \"{src}\") p{p.name}\n\n"
  let allNames := " ++ ".intercalate (l.paras.map (s!"p{·.name}"))
  out := out ++ s!"def owner : List Nat := {reprStr owner}\n\n"
  out := out ++ "/-- The story with its solved timeline (minutes); `Timed.Valid` re-checks it. -/\n"
  out := out ++ s!"def story : Timed (E spec) :=\n  \{ told := ({if l.paras.isEmpty then "[]" else allNames}).map (Ev.toE spec),\n" ++
    s!"    constraints := {lean (reprStr story.constraints)},\n    metric := {lean (reprStr story.metric)},\n" ++
    s!"    timeline := {lean (reprStr timed.timeline)} }\n\n"
  let chrono := timed.chrono
  let whole := if validB s.start chrono then "Valid" else if plausibleB s.start chrono then "Plausible" else "¬Plausible"
  out := out ++ match whole with
    | "Valid" => "theorem story_valid : story.Valid spec.start := by decide +kernel\n\n"
    | "Plausible" => "theorem story_plausible : story.Plausible spec.start := by decide +kernel\n\n"
    | _ => "theorem story_fails : ¬ story.Plausible spec.start := by decide +kernel\n\n"
  for (p, k) in l.paras.zipIdx do
    let es := timed.upTo owner k
    let nm := p.name
    let up := s!"(story.upTo owner {k})"
    if validB s.start es then
      out := out ++ s!"theorem p{nm}_valid : Valid spec.start {up} := by decide +kernel\n"
    else if plausibleB s.start es then
      out := out ++ s!"theorem p{nm}_plausible : Plausible spec.start {up} := by decide +kernel\n"
      out := out ++ s!"theorem p{nm}_assumes : assumedAt spec.start {up} 0 = {reprStr (assumedAt s.start es 0)} := by decide +kernel\n"
    else
      out := out ++ s!"theorem p{nm}_fails : ¬ Plausible spec.start {up} := by decide +kernel\n"
    let w := run s.start es
    for (c, j) in p.claims.zipIdx do
      match n.claim c with
      | .ok cl =>
        let b := cl.eval w
        out := out ++ s!"/-- {c} -/\ntheorem p{nm}_claim{j} : ({lean (reprStr cl)}).eval (run spec.start {up}) = {b} := by decide +kernel\n"
      | .error _ => pure ()
    if let some plan := p.plan then
      if p.items.any (·.src != "plan") then
        let r := decide (Refines some (p.items.map (·.ev)) plan)
        out := out ++ s!"theorem p{nm}_realises : {if r then "" else "¬ "}Refines some p{nm} {lean (reprStr plan)} := by decide +kernel\n"
    out := out ++ "\n"
  if let some B := l.beats then
    let ids := B.vocab.map (·.id)
    let coarse : List Nat := l.beatStory.filterMap ids.idxOf?
    let fine := l.paras.flatMap fun p => p.plan.getD (p.items.map (·.ev))
    out := out ++ s!"def beats : Beats := {lean (reprStr B)}\n\n"
    out := out ++ s!"def beatStory : List (BeatEv beats) := {reprStr coarse}.map (⟨·⟩)\n\n"
    out := out ++ s!"def plans : List Ev := {lean (reprStr fine)}\n\n"
    let bv := decide (Valid B.start (coarse.map (⟨·⟩ : Nat → BeatEv B)))
    out := out ++ s!"theorem beats_{if bv then "valid" else "invalid"} : {if bv then "" else "¬ "}Valid beats.start beatStory := by decide +kernel\n"
    let rf := decide (Refines B.abs fine (coarse.map (⟨·⟩ : Nat → BeatEv B)))
    out := out ++ s!"theorem plans_{if rf then "refine" else "do_not_refine"}_beats : {if rf then "" else "¬ "}Refines beats.abs plans beatStory := by decide +kernel\n\n"
  out := out ++ s!"end {ns}\n"
  pure out

end LangLib.Studio
