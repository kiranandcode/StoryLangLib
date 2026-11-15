import LangLib.Studio.Complete

/-!
# Story directories

```
stories/<name>/
  story.json                 the world (see `Parse.lean`), beats, fact lexicon
  paragraphs/NN.txt          the prose of paragraph NN
  paragraphs/NN.plan.json    {"beat": "...", "events": [...], "claims": [...]}
  paragraphs/NN.json         its langlib annotation
  paragraphs/NN.events.json  {"events": [{"e": "...", "at": 12, "phase": "main"}], "claims": [...],
                              "staging": [{"s": "leftOf rdesk kdesk", "at": 110, "w": "left"}]}
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
    let mut staging : List Fixed := []
    let mut stagingAt : List (Option Nat × Option String) := []
    -- a plan names the setting its paragraph will use (`setting`, `staging`)
    let mut planSetting : List Spot := []
    if let some pj := planJ then
      for x in strs pj "setting" do
        match n.spot x with
        | .ok sp => planSetting := planSetting ++ [sp]
        | .error m => errors := errors ++ [s!"plan setting: {m}"]
    for ej in (evJ <|> (if doc.isNone then planJ else none)).toList do
      for it in arr ej "staging" do
        let str := (it.getStr?.toOption <|> (it.getObjValAs? String "s").toOption).getD ""
        match n.fixed str with
        | .ok f =>
          staging := staging ++ [f]
          stagingAt := stagingAt ++ [((it.getObjValAs? Nat "at").toOption, (it.getObjValAs? String "w").toOption)]
        | .error m => errors := errors ++ [s!"staging: {m}"]
    -- claims written as strings are about the end of the paragraph; anchored ones
    -- ({"c": ..., "at": ...}) are judgements at their token (`Complete.lean`)
    let claimStrs (j : Json) : List String := (arr j "claims").filterMap (·.getStr?.toOption)
    let claims := (evJ.map claimStrs).getD [] ++ (planJ.map claimStrs).getD []
    let beat := planJ.bind fun pj => (pj.getObjValAs? String "beat").toOption
    pure ({ name := nm, text, doc, plan, items, claims := claims.eraseDups, beat, errors, staging, stagingAt,
            planSetting, reading := evJ } : Para)
  pure { spec, beats, beatStory, lex, paras }

/-- A paragraph's context for completeness: the story before it, and its events
with their tokens. -/
def paraCtx (s : Spec) (timed : Timed (E s)) (owner : List Nat) (k : Nat) (p : Para) : ParaCtx s :=
  { prior := if k == 0 then [] else timed.upTo owner (k - 1),
    items := p.items.map fun it => (it.ev, it.at_.getD 0) }

/-- What keeps a paragraph from being complete, in words. -/
def paraCompleteness (s : Spec) (c : ParaCtx s) (p : Para) : List String :=
  -- every paragraph with prose must be complete; a planned one has nothing to judge yet
  if p.text.trimAscii.isEmpty then [] else
  match p.doc, p.reading with
  | some d, some j =>
    match judgesOf s j with
    | .error e => [s!"judgements: {e}"]
    | .ok js =>
      (unanchoredClaims j).map (fun c =>
        s!"the claim \"{c}\" has no anchor: write it as \{\"c\": ..., \"at\": token, \"w\": word}") ++
      completeIssues c (treeFacts s d) js d.render
  | none, _ => ["no annotation to judge"]
  | _, none => ["no reading to judge"]

def storyReport (dir : System.FilePath) : IO Json := do
  let l ← loadStory dir
  let r := report l.spec l.beats l.beatStory l.lex l.paras
  let s := l.spec
  let (story, owner) := storyOf (s := s) l.paras
  let some timed := story.solved | return r
  let owner := owner.map (·.2)
  let cs := l.paras.zipIdx.map fun (p, k) =>
    let issues := paraCompleteness s (paraCtx s timed owner k p) p
    let f := (p.doc.map (treeFacts s)).getD {}
    let toks : List String := (p.doc.map (·.render)).getD []
    let n := s.names
    let one (at_ : Nat) (kind text gloss : String) : Json :=
      Json.mkObj [("at", at_), ("kind", kind), ("text", text), ("gloss", gloss)]
    let judgesJ : List Json := match p.reading with
      | none => []
      | some j =>
        ((arr j "events").filterMap fun e => do
          let a ← (e.getObjValAs? Nat "at").toOption
          let str ← (e.getObjValAs? String "e").toOption
          pure (one a "event" str (match n.ev str with | .ok ev => s.evGloss ev | .error _ => str))) ++
        ((arr j "claims").filterMap fun c => do
          let a ← (c.getObjValAs? Nat "at").toOption
          let str ← (c.getObjValAs? String "c").toOption
          pure (one a "claim" str str)) ++
        ((arr j "judge").filterMap fun x => do
          let a ← (x.getObjValAs? Nat "at").toOption
          let kind := (x.getObjValAs? String "kind").toOption.getD ""
          let lit := (x.getObjValAs? String "lit").toOption
          let e := (x.getObjValAs? String "e").toOption
          let text := (lit <|> e).getD kind
          let gloss := match lit with
            | some l => match n.lit l with | .ok l => s.litGloss l | .error _ => l
            | none => text
          pure (one a kind text gloss))
    Json.mkObj [("name", p.name), ("issues", Json.arr (issues.map Json.str).toArray),
      ("clauses", Json.arr (f.preds.map fun c => Json.mkObj [("at", c.at_), ("w", Json.str (toks.getD c.at_ "")),
        ("span", Json.arr ((((p.doc.map clauseSpans).getD []).find? (·.1 == c.at_)).map (·.2) |>.getD [c.at_]
          |>.map (fun (i : Nat) => Json.num i) |>.toArray)),
        ("neg", c.neg), ("modal", c.modal), ("quoted", c.quoted),
        ("parent", match c.parent with | some q => Json.num q | none => Json.null)]).toArray),
      ("links", Json.arr (f.links.map fun l => Json.mkObj [("at", l.at_), ("word", l.word),
        ("rel", reprStr l.rel |>.replace "LangLib.Studio.LinkRel." ""), ("a", l.a), ("b", l.b)]).toArray),
      ("judges", Json.arr judgesJ.toArray),
      ("trees", Json.arr (((p.doc.map (·.sentences)).getD []).map (·.tree.toJson)).toArray),
      ("derivations", match p.doc, (p.reading.map (judgesOf s)) with
        | some d, some (.ok js) => Json.arr ((derivations (paraCtx s timed owner k p) f js toks).map fun (a, dv) =>
            Json.mkObj [("at", a), ("d", dv.toJson)]).toArray
        | _, _ => Json.arr #[])]
  let pdata : List (ParaData s) := l.paras.zipIdx.filterMap fun (p, k) =>
    match p.doc, p.reading.map (judgesOf s) with
    | some d, some (.ok js) => some (p.name, paraCtx s timed owner k p, treeFacts s d, js, d.render)
    | _, _ => none
  pure ((r.setObjVal! "completeness" (Json.arr cs.toArray)).setObjVal! "argument"
    (argumentJson (argumentGraph s pdata)))

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

/-- A paragraph's annotation still reads as `u`. -/
def usesMatch (s : Spec) (str : String) (u : Uses) : Bool :=
  match docOfString str with
  | .ok d => usesOf s d == u
  | .error _ => false

/-- A paragraph's events file still stages `st`. -/
def stagingMatch (s : Spec) (str : String) (st : List Fixed) : Bool :=
  match Json.parse str with
  | .ok j =>
    let xs := match j.getObjVal? "staging" with
      | .ok (.arr a) => a.toList.filterMap fun (e : Json) =>
        (e.getStr?.toOption <|> (e.getObjValAs? String "s").toOption)
      | _ => []
    (xs.mapM s.names.fixed).toOption == some st
  | .error _ => false

/-- A plan still names `xs` as its setting. -/
def planSettingMatch (s : Spec) (str : String) (xs : List Spot) : Bool :=
  match Json.parse str with
  | .ok j =>
    let ids := ((j.getObjValAs? (Array String) "setting").toOption.getD #[]).toList
    (ids.mapM s.names.spot).toOption == some xs
  | .error _ => false

/-- One-line `repr` (structure instances must not wrap below their first field). -/
private def rs {α : Type} [Repr α] (a : α) : String := (repr a).pretty 1000000

private def lean (s : String) : String :=
  -- `reprStr` output is Lean syntax; drop the namespaces we open
  ((s.replace "LangLib.Studio." "").replace "LangLib.World." "")

/-- The story as a Lean file with checkpoints (`Snap.lean`): the state after each
paragraph is a literal, each paragraph's verdicts are proved from the checkpoint
before it, and the lemmas there chain them into statements from the story's start.
Kernel work is one replay of the story, not one per paragraph. Used when every
paragraph's events extend the story in time order (no flashback moves an event
before an earlier paragraph's), and the story is at least plausible. -/
def storyLeanSnap (l : Loaded) (ns : String) (timed : Timed (E l.spec)) (owner : List Nat)
    (story : Story (E l.spec)) : Option String := Id.run do
  let s := l.spec
  let n := s.names
  if l.paras.isEmpty then return none
  -- each paragraph's events in story time must extend the ones before
  let ups := (List.range l.paras.length).map (timed.upTo owner ·)
  let ok := (ups.zipIdx.all fun (es, k) =>
    let prev := if k == 0 then [] else ups.getD (k - 1) []
    es.take prev.length == prev) && ups.getLast? == some timed.chrono
  if !ok then return none
  let chrono := timed.chrono
  let whole := if validB s.start chrono then "Valid" else if plausibleB s.start chrono then "Plausible" else "no"
  if whole == "no" then return none
  let pred := if whole == "Valid" then "Valid" else "Plausible"
  let mut out := s!"import LangLib.Studio\n\n/-!\n# {ns}: generated by `langlib story-lean`\n\n" ++
    "Every theorem here restates a verdict of the Studio's report and is proved by\n" ++
    "`decide +kernel`, from checkpoints (`LangLib/Studio/Snap.lean`): `cNN` is the\n" ++
    "state after paragraph NN, `pNN_step` proves it from the one before, each\n" ++
    "paragraph's verdicts are proved from the checkpoint it opens in, and\n" ++
    "`pNN_valid` chains them into the story from its start. Regenerate after editing\n" ++
    "the story; the `#guard` lines fail if the story files no longer match.\n-/\n\n" ++
    s!"namespace {ns}\nopen LangLib.World LangLib.Studio\n\n" ++
    "-- the kernel walks long lists of beliefs recursively\nset_option maxRecDepth 100000\n\n"
  out := out ++ s!"def spec : Spec := {lean (rs s)}\n\n"
  out := out ++ "#guard specMatches (include_str \"story.json\") spec\n\n"
  for p in l.paras do
    let evs := p.items.map (·.ev)
    out := out ++ s!"/-- paragraph {p.name} -/\ndef p{p.name} : List Ev := {lean (rs evs)}\n"
    let src := if p.items.any (·.src != "plan") then s!"paragraphs/{p.name}.events.json" else s!"paragraphs/{p.name}.plan.json"
    if !p.items.isEmpty || p.plan.isSome then
      out := out ++ s!"#guard eventsMatch spec (include_str \"{src}\") p{p.name}\n"
    out := out ++ "\n"
  let allNames := " ++ ".intercalate (l.paras.map (s!"p{·.name}"))
  out := out ++ s!"def owner : List Nat := {rs owner}\n\n"
  out := out ++ "/-- The story with its solved timeline (minutes); `Timed.Valid` re-checks it. -/\n"
  out := out ++ s!"def story : Timed (E spec) :=\n  \{ told := ({allNames}).map (Ev.toE spec),\n" ++
    s!"    constraints := {lean (rs story.constraints)},\n    metric := {lean (rs story.metric)},\n" ++
    s!"    timeline := {lean (rs timed.timeline)} }\n\n"
  let mut w := s.start
  let mut seen : List (Nat × Bool) := []
  let mut prevName := ""
  let mut prefix_ := ""
  for (p, k) in l.paras.zipIdx do
    let nm := p.name
    let prevEs := if k == 0 then [] else ups.getD (k - 1) []
    let chunk := (ups.getD k []).drop prevEs.length
    let cPrev := if k == 0 then "spec.start" else s!"c{prevName}"
    let sPrev := if k == 0 then "[]" else s!"s{prevName}"
    let w' := run w chunk
    prefix_ := if k == 0 then s!"chunk{nm}" else s!"({prefix_} ++ chunk{nm})"
    out := out ++ s!"def chunk{nm} : List (E spec) := {lean (rs chunk)}\n"
    if chunk.isEmpty then
      out := out ++ s!"def c{nm} : W spec := {cPrev}\n"
      out := out ++ s!"theorem p{nm}_step : run {cPrev} chunk{nm} = c{nm} := rfl\n"
    else
      out := out ++ s!"def c{nm} : W spec := {lean (rs w')}\n"
      out := out ++ s!"theorem p{nm}_step : run {cPrev} chunk{nm} = c{nm} := by decide +kernel\n"
    out := out ++ s!"theorem p{nm}_here : {pred} {cPrev} chunk{nm} := by decide +kernel\n"
    if whole == "Plausible" then
      out := out ++ s!"theorem p{nm}_assumes : assumedAt {cPrev} chunk{nm} 0 = {rs (assumedAt w chunk 0)} := by decide +kernel\n"
    if k == 0 then
      out := out ++ s!"theorem p{nm}_{pred.decapitalize} : {pred} spec.start {prefix_} := p{nm}_here\n"
      out := out ++ s!"theorem p{nm}_run : run spec.start {prefix_} = c{nm} := p{nm}_step\n"
    else
      out := out ++ s!"theorem p{nm}_{pred.decapitalize} : {pred} spec.start {prefix_} :=\n  " ++
        s!"{pred}.chain p{prevName}_{pred.decapitalize} p{prevName}_run p{nm}_here\n"
      out := out ++ s!"theorem p{nm}_run : run spec.start {prefix_} = c{nm} := run_chain p{prevName}_run p{nm}_step\n"
    for (c, j) in p.claims.zipIdx do
      match n.claim c with
      | .ok cl =>
        out := out ++ s!"/-- {c} -/\ntheorem p{nm}_claim{j} : ({lean (rs cl)}).eval c{nm} = {cl.eval w'} := by decide +kernel\n"
      | .error _ => pure ()
    if s.hasSetting then
      if let some d := p.doc then
        let u := usesOf s d
        out := out ++ s!"def p{nm}uses : Uses := {lean (rs u)}\n"
        out := out ++ s!"#guard usesMatch spec (include_str \"paragraphs/{nm}.json\") p{nm}uses\n"
        out := out ++ s!"def p{nm}staging : List Fixed := {lean (rs p.staging)}\n"
        if !p.staging.isEmpty then
          out := out ++ s!"#guard stagingMatch spec (include_str \"paragraphs/{nm}.events.json\") p{nm}staging\n"
        out := out ++ s!"theorem p{nm}_setting : spec.settingOk (sceneOf {cPrev} chunk{nm} 0) p{nm}uses p{nm}staging = true := by decide +kernel\n"
        if s.pov.isSome then
          let (_, seen') := perceptFrom w seen (k == 0) chunk (p.mentioned s)
          out := out ++ s!"def s{nm} : List (Nat × Bool) := {rs seen'}\n"
          out := out ++ s!"theorem p{nm}_perceived : perceptFrom {cPrev} {sPrev} {k == 0} chunk{nm} {rs (p.mentioned s)} = ([], s{nm}) := by decide +kernel\n"
          seen := seen'
      if p.doc.isNone && p.plan.isSome then
        out := out ++ s!"def p{nm}setting : List Spot := {lean (rs p.planSetting)}\n"
        out := out ++ s!"#guard planSettingMatch spec (include_str \"paragraphs/{nm}.plan.json\") p{nm}setting\n"
        out := out ++ s!"def p{nm}staging : List Fixed := {lean (rs p.staging)}\n"
        if !p.staging.isEmpty then
          out := out ++ s!"#guard stagingMatch spec (include_str \"paragraphs/{nm}.plan.json\") p{nm}staging\n"
        out := out ++ s!"theorem p{nm}_setting : spec.planSettingOk (sceneOf {cPrev} chunk{nm} 0) p{nm}setting p{nm}staging = true := by decide +kernel\n"
    if s.pov.isSome && !(s.hasSetting && p.doc.isSome) then
      -- keep the point of view's memory flowing through paragraphs without a perception check
      let (_, seen') := perceptFrom w seen (k == 0) chunk (p.mentioned s)
      out := out ++ s!"def s{nm} : List (Nat × Bool) := {rs seen'}\n"
      out := out ++ s!"theorem p{nm}_seen : (perceptFrom {cPrev} {sPrev} {k == 0} chunk{nm} {rs (p.mentioned s)}).2 = s{nm} := by decide +kernel\n"
      seen := seen'
    if let (some d, some j) := (p.doc, p.reading) then
      if let .ok js := judgesOf s j then
        let f := treeFacts s d
        out := out ++ s!"def p{nm}tree : TreeFacts := {lean (rs f)}\n"
        out := out ++ s!"#guard treeMatch spec (include_str \"paragraphs/{nm}.json\") p{nm}tree\n"
        out := out ++ s!"def p{nm}judges : List Judge := {lean (rs js)}\n"
        out := out ++ s!"#guard judgesMatch spec (include_str \"paragraphs/{nm}.events.json\") p{nm}judges\n"
        let ats := p.items.map (·.at_.getD 0)
        out := out ++ s!"theorem p{nm}_complete : completeOk (\{ prior := [], items := p{nm}.zip {rs ats}, base := {cPrev} } : ParaCtx spec) p{nm}tree p{nm}judges = true := by decide +kernel\n"
    if let some plan := p.plan then
      if p.items.any (·.src != "plan") then
        let r := decide (Refines some (p.items.map (·.ev)) plan)
        out := out ++ s!"theorem p{nm}_realises : {if r then "" else "¬ "}Refines some p{nm} {lean (rs plan)} := by decide +kernel\n"
    out := out ++ "\n"
    w := w'
    prevName := nm
  out := out ++ s!"theorem story_chrono : story.chrono = {prefix_} := by decide +kernel\n"
  out := out ++ s!"theorem story_{pred.decapitalize} : story.{pred} spec.start :=\n  " ++
    s!"Timed.{pred.decapitalize}_of (by decide +kernel) story_chrono p{prevName}_{pred.decapitalize}\n\n"
  if s.hasSetting then
    out := out ++ "theorem layout_consistent : spec.layoutOk = true := by decide +kernel\n\n"
  if let some B := l.beats then
    let ids := B.vocab.map (·.id)
    let coarse : List Nat := l.beatStory.filterMap ids.idxOf?
    let fine := l.paras.flatMap fun p => p.plan.getD (p.items.map (·.ev))
    out := out ++ s!"def beats : Beats := {lean (rs B)}\n\n"
    out := out ++ s!"def beatStory : List (BeatEv beats) := {rs coarse}.map (⟨·⟩)\n\n"
    out := out ++ s!"def plans : List Ev := {lean (rs fine)}\n\n"
    let bv := decide (Valid B.start (coarse.map (⟨·⟩ : Nat → BeatEv B)))
    out := out ++ s!"theorem beats_{if bv then "valid" else "invalid"} : {if bv then "" else "¬ "}Valid beats.start beatStory := by decide +kernel\n"
    let rf := decide (Refines B.abs fine (coarse.map (⟨·⟩ : Nat → BeatEv B)))
    out := out ++ s!"theorem plans_{if rf then "refine" else "do_not_refine"}_beats : {if rf then "" else "¬ "}Refines beats.abs plans beatStory := by decide +kernel\n\n"
  out := out ++ s!"end {ns}\n"
  return some out

def storyLean (dir : System.FilePath) (ns : String) : IO String := do
  let l ← loadStory dir
  let s := l.spec
  let n := s.names
  let (story, owner) := storyOf (s := s) l.paras
  let some timed := story.solved
    | throw (IO.userError "the story's time constraints have no solution")
  let owner := owner.map (·.2)
  if let some src := storyLeanSnap l ns timed owner story then return src
  let mut out := s!"import LangLib.Studio\n\n/-!\n# {ns}: generated by `langlib story-lean`\n\n" ++
    "Every theorem here restates a verdict of the Studio's report and is proved by\n" ++
    "`decide +kernel`. Regenerate after editing the story; the `#guard` lines fail if\n" ++
    "the story files no longer match the definitions below.\n-/\n\n" ++
    s!"namespace {ns}\nopen LangLib.World LangLib.Studio\n\n"
  out := out ++ s!"def spec : Spec := {lean (rs s)}\n\n"
  out := out ++ "#guard specMatches (include_str \"story.json\") spec\n\n"
  let paraEvs := l.paras.map fun p => p.items.map (·.ev)
  for (p, evs) in l.paras.zip paraEvs do
    out := out ++ s!"/-- paragraph {p.name} -/\ndef p{p.name} : List Ev := {lean (rs evs)}\n"
    let src := if p.items.any (·.src != "plan") then s!"paragraphs/{p.name}.events.json" else s!"paragraphs/{p.name}.plan.json"
    if !p.items.isEmpty || p.plan.isSome then
      out := out ++ s!"#guard eventsMatch spec (include_str \"{src}\") p{p.name}\n"
    out := out ++ "\n"
  let allNames := " ++ ".intercalate (l.paras.map (s!"p{·.name}"))
  out := out ++ s!"def owner : List Nat := {rs owner}\n\n"
  out := out ++ "/-- The story with its solved timeline (minutes); `Timed.Valid` re-checks it. -/\n"
  out := out ++ s!"def story : Timed (E spec) :=\n  \{ told := ({if l.paras.isEmpty then "[]" else allNames}).map (Ev.toE spec),\n" ++
    s!"    constraints := {lean (rs story.constraints)},\n    metric := {lean (rs story.metric)},\n" ++
    s!"    timeline := {lean (rs timed.timeline)} }\n\n"
  let chrono := timed.chrono
  let whole := if validB s.start chrono then "Valid" else if plausibleB s.start chrono then "Plausible" else "¬Plausible"
  out := out ++ match whole with
    | "Valid" => "theorem story_valid : story.Valid spec.start := by decide +kernel\n\n"
    | "Plausible" => "theorem story_plausible : story.Plausible spec.start := by decide +kernel\n\n"
    | _ => "theorem story_fails : ¬ story.Plausible spec.start := by decide +kernel\n\n"
  -- Verdicts the report has computed (true by construction) go into one theorem:
  -- the paragraphs' runs share prefixes, which the kernel then reduces once, so
  -- checking is linear in the story rather than quadratic. Each is restated under
  -- its own name. A claim that may be false (the setting) stands alone, so it fails
  -- on its own.
  let mut bundled : Array (String × String × String) := #[]  -- (name, statement, doc)
  for (p, k) in l.paras.zipIdx do
    let es := timed.upTo owner k
    let nm := p.name
    let up := s!"(story.upTo owner {k})"
    if validB s.start es then
      bundled := bundled.push (s!"p{nm}_valid", s!"Valid spec.start {up}", "")
    else if plausibleB s.start es then
      bundled := bundled.push (s!"p{nm}_plausible", s!"Plausible spec.start {up}", "")
      bundled := bundled.push (s!"p{nm}_assumes", s!"assumedAt spec.start {up} 0 = {rs (assumedAt s.start es 0)}", "")
    else
      bundled := bundled.push (s!"p{nm}_fails", s!"¬ Plausible spec.start {up}", "")
    let w := run s.start es
    for (c, j) in p.claims.zipIdx do
      match n.claim c with
      | .ok cl =>
        let b := cl.eval w
        bundled := bundled.push (s!"p{nm}_claim{j}", s!"({lean (rs cl)}).eval (run spec.start {up}) = {b}", c)
      | .error _ => pure ()
    if s.hasSetting then
      if let some d := p.doc then
        let u := usesOf s d
        let prev := if k == 0 then 0 else (timed.upTo owner (k - 1)).length
        out := out ++ s!"def p{nm}uses : Uses := {lean (rs u)}\n"
        out := out ++ s!"#guard usesMatch spec (include_str \"paragraphs/{nm}.json\") p{nm}uses\n"
        out := out ++ s!"def p{nm}staging : List Fixed := {lean (rs p.staging)}\n"
        if !p.staging.isEmpty then
          out := out ++ s!"#guard stagingMatch spec (include_str \"paragraphs/{nm}.events.json\") p{nm}staging\n"
        -- claimed true whatever the verdict: a paragraph that breaks the setting fails its proof
        let stmt := s!"spec.settingOk (sceneOf spec.start {up} {prev}) p{nm}uses p{nm}staging = true"
        if s.settingOk (sceneOf s.start es prev) u p.staging then
          bundled := bundled.push (s!"p{nm}_setting", stmt, "")
        else
          out := out ++ s!"theorem p{nm}_setting : {stmt} := by decide +kernel\n"
        if s.pov.isSome then
          let mentioned := p.mentioned s
          let wst := s!"spec.perceptOk spec.start {up} {prev} {rs mentioned} = true"
          if s.perceptOk s.start es prev mentioned then
            bundled := bundled.push (s!"p{nm}_perceived", wst, "")
          else
            out := out ++ s!"theorem p{nm}_perceived : {wst} := by decide +kernel\n"
      if p.doc.isNone && p.plan.isSome then
        let prev := if k == 0 then 0 else (timed.upTo owner (k - 1)).length
        out := out ++ s!"def p{nm}setting : List Spot := {lean (rs p.planSetting)}\n"
        out := out ++ s!"#guard planSettingMatch spec (include_str \"paragraphs/{nm}.plan.json\") p{nm}setting\n"
        out := out ++ s!"def p{nm}staging : List Fixed := {lean (rs p.staging)}\n"
        if !p.staging.isEmpty then
          out := out ++ s!"#guard stagingMatch spec (include_str \"paragraphs/{nm}.plan.json\") p{nm}staging\n"
        let stmt := s!"spec.planSettingOk (sceneOf spec.start {up} {prev}) p{nm}setting p{nm}staging = true"
        if s.planSettingOk (sceneOf s.start es prev) p.planSetting p.staging then
          bundled := bundled.push (s!"p{nm}_setting", stmt, "")
        else
          out := out ++ s!"theorem p{nm}_setting : {stmt} := by decide +kernel\n"
    if let (some d, some j) := (p.doc, p.reading) then
      if let .ok js := judgesOf s j then
        let f := treeFacts s d
        out := out ++ s!"def p{nm}tree : TreeFacts := {lean (rs f)}\n"
        out := out ++ s!"#guard treeMatch spec (include_str \"paragraphs/{nm}.json\") p{nm}tree\n"
        out := out ++ s!"def p{nm}judges : List Judge := {lean (rs js)}\n"
        out := out ++ s!"#guard judgesMatch spec (include_str \"paragraphs/{nm}.events.json\") p{nm}judges\n"
        let ats := p.items.map (·.at_.getD 0)
        let prior := if k == 0 then "[]" else s!"story.upTo owner {k - 1}"
        let stmt := s!"completeOk (⟨{prior}, p{nm}.zip {rs ats}⟩ : ParaCtx spec) p{nm}tree p{nm}judges = true"
        let ok := (unanchoredClaims j).isEmpty && completeOk (paraCtx s timed owner k p) f js
        if ok then bundled := bundled.push (s!"p{nm}_complete", stmt, "")
        else out := out ++ s!"theorem p{nm}_complete : {stmt} := by decide +kernel\n"
    if let some plan := p.plan then
      if p.items.any (·.src != "plan") then
        let r := decide (Refines some (p.items.map (·.ev)) plan)
        bundled := bundled.push (s!"p{nm}_realises", s!"{if r then "" else "¬ "}Refines some p{nm} {lean (rs plan)}", "")
    out := out ++ "\n"
  if !bundled.isEmpty then
    out := out ++ "/-- Every paragraph's verdicts, checked together (see `storyLean`); each is\n" ++
      "restated below under its own name. -/\ntheorem paragraphs :\n    " ++
      " ∧\n    ".intercalate (bundled.toList.map fun (_, st, _) => s!"({st})") ++ " := by\n  decide +kernel\n\n"
    for ((name, st, doc), i) in bundled.toList.zipIdx do
      let proj := String.join (List.replicate i ".2") ++ (if i + 1 == bundled.size then "" else ".1")
      if doc != "" then out := out ++ s!"/-- {doc} -/\n"
      out := out ++ s!"theorem {name} : {st} := by exact paragraphs{proj}\n"
    out := out ++ "\n"
  if s.hasSetting then
    out := out ++ "theorem layout_consistent : spec.layoutOk = true := by decide +kernel\n\n"
  if let some B := l.beats then
    let ids := B.vocab.map (·.id)
    let coarse : List Nat := l.beatStory.filterMap ids.idxOf?
    let fine := l.paras.flatMap fun p => p.plan.getD (p.items.map (·.ev))
    out := out ++ s!"def beats : Beats := {lean (rs B)}\n\n"
    out := out ++ s!"def beatStory : List (BeatEv beats) := {rs coarse}.map (⟨·⟩)\n\n"
    out := out ++ s!"def plans : List Ev := {lean (rs fine)}\n\n"
    let bv := decide (Valid B.start (coarse.map (⟨·⟩ : Nat → BeatEv B)))
    out := out ++ s!"theorem beats_{if bv then "valid" else "invalid"} : {if bv then "" else "¬ "}Valid beats.start beatStory := by decide +kernel\n"
    let rf := decide (Refines B.abs fine (coarse.map (⟨·⟩ : Nat → BeatEv B)))
    out := out ++ s!"theorem plans_{if rf then "refine" else "do_not_refine"}_beats : {if rf then "" else "¬ "}Refines beats.abs plans beatStory := by decide +kernel\n\n"
  out := out ++ s!"end {ns}\n"
  pure out

end LangLib.Studio
