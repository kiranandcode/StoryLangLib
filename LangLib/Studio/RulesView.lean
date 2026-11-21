import Lean.Data.Json
import LangLib.World.Rules
import LangLib.Studio.PaperArg

/-!
# An argument's inferences as informal rules, for the Studio and deslop

`langlib rules <dir>` reads the same files as `langlib argument`
(`<dir>/argument.json` and `<dir>/paragraphs/NN.argument.json`) and prints
each inference as a rule (`World/Rules`): its premises with their tags and
verbatim quotes, its conclusion, strict or defeasible, its scheme, its
critical questions (answered, open, or pressed), the attacks on it, and its
grounded label with and without the sceptic's questions.

An `infer` move carries its rule in a `rule` field (`roles` names the part
each premise plays in the scheme, e.g. "needs" and "provides"):

```
{"move": "infer", "t": "k", "premises": ["p", "q"], "uses": [],
 "rule": {"id": "R3", "kind": "defeasible", "scheme": "exampleToGen",
          "quote": "...", "tags": {"p": "example"}, "quotes": {"p": "..."},
          "answered": [0], "pressed": [2], "notes": {"2": "..."},
          "attacks": [{"tgt": "R0", "how": "undercut", "on": null, "quote": "..."}]}}
```

A premise's tag, when the rule does not give one, comes from the move that
put it forward: a citation, an example, a hedge, a promise or contribution,
lore or a definition (a fact), a claim (the authors' word, or a fact when
`argument.json`'s `terms` say its kind is `fact`). `argument.json` may list
`opponents` (rules for positions the text argues against, in the same shape
with a `concl`) and a `root` (the overall conclusion).
-/

namespace LangLib.Studio.RulesView
open Lean LangLib.World LangLib.World.Argument

private def strs (j : Json) (k : String) : List String :=
  match j.getObjVal? k with
  | .ok (.arr a) => a.toList.filterMap (·.getStr?.toOption)
  | _ => []
private def nats (j : Json) (k : String) : List Nat :=
  match j.getObjVal? k with
  | .ok (.arr a) => a.toList.filterMap (·.getNat?.toOption)
  | _ => []
private def str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
private def obj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD (Json.mkObj [])
private def field (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def schemeOf : String → Option Scheme
  | "deductive" => some .deductive | "definitional" => some .definitional
  | "exampleToGen" => some .exampleToGen | "practical" => some .practical
  | "abduction" => some .abduction | "trackRecord" => some .trackRecord
  | "expertOpinion" => some .expertOpinion | "causeToEffect" => some .causeToEffect
  | "analogy" => some .analogy | "requirement" => some .requirement
  | "counterexample" => some .counterexample | _ => none

def schemeByName (n : String) : Option Scheme :=
  match schemeOf n with
  | some s => some s
  | none => match n with
    | "perception" => some .perception | "testimony" | "witness testimony" => some .testimony
    | "sign" => some .sign | "ruleApp" | "rule application" => some .ruleApp | "unread" => some .unread
    | _ => ([Scheme.deductive, .definitional, .exampleToGen, .practical, .abduction, .trackRecord, .expertOpinion,
        .causeToEffect, .analogy, .requirement, .counterexample].find? (·.name == n))

def slotS : Slot → String
  | .premise => "premise" | .definition => "definition" | .general => "general" | .instance => "instance"
  | .condition => "condition" | .limit => "limit" | .goal => "goal" | .problem => "problem" | .means => "means"
  | .feasible => "feasible" | .who => "who" | .needs => "needs" | .provides => "provides" | .case => "case"
  | .result => "result" | .observed => "observed" | .explanation => "explanation" | .rival => "rival"
  | .principle => "principle" | .cause => "cause" | .effect => "effect" | .source => "source"
  | .target => "target" | .similarity => "similarity" | .pastWork => "pastWork"
  | .selfAssessment => "selfAssessment" | .expert => "expert" | .perceived => "perceived" | .said => "said"
  | .witness => "witness" | .access => "access" | .sign => "sign"

def allSlots : List Slot :=
  [.premise, .definition, .general, .instance, .condition, .limit, .goal, .problem, .means, .feasible, .who,
   .needs, .provides, .case, .result, .observed, .explanation, .rival, .principle, .cause, .effect, .source,
   .target, .similarity, .pastWork, .selfAssessment, .expert, .perceived, .said, .witness, .access, .sign]

def slotOfS (s : String) : Option Slot := allSlots.find? (slotS · == s)

def faultJ : Fault String → Json
  | .unslotted p => Json.mkObj [("kind", "unslotted"), ("t", p), ("why", s!"premise {p} fills no slot of its scheme")]
  | .illegal p sl => Json.mkObj [("kind", "illegal"), ("t", p), ("slot", slotS sl), ("why", s!"premise {p} as {sl.name}: not a slot of this scheme")]
  | .fanIn n => Json.mkObj [("kind", "fanIn"), ("n", n), ("why", s!"{n} premises: group them (at most {maxFanIn})")]
  | .empty => Json.mkObj [("kind", "empty"), ("why", "a defeasible rule with no premises")]
  | .unread => Json.mkObj [("kind", "unread"), ("why", "no scheme read yet")]

def tagOf : String → Option Tag
  | "fact" => some .fact | "example" => some .«example» | "citation" => some .citation
  | "authors" => some .authors | "hedge" => some .hedge | "promise" => some .promise | _ => none

def tagS : Tag → String
  | .fact => "fact" | .«example» => "example" | .citation => "citation"
  | .authors => "authors" | .hedge => "hedge" | .promise => "promise"

def howOf : String → Option AttackKind
  | "rebut" => some .rebut | "undercut" => some .undercut | "undermine" => some .undermine | _ => none

def howS : AttackKind → String
  | .rebut => "rebut" | .undercut => "undercut" | .undermine => "undermine"

def labS : Lab → String
  | .in => "in" | .out => "out" | .undec => "undec"

def thinS : Thin → String
  | .fewExamples n => s!"a generalisation from {n} example{if n == 1 then "" else "s"}"
  | .onPromise => "rests on a promise (something not yet done)"
  | .authorsWord => "every premise rests on the authors' word"

/-- What we keep beside each rule for display. -/
structure Info where
  id : String
  para : String
  quote : String
  quotes : Json
  notes : Json
  roles : Json := Json.mkObj []
  attacks : List Json

/-- The tag of a term from the move that put it forward. -/
def tagFromMoves (kinds : Json) (lore : List String) (seen : List (String × String)) (t : String) : Tag :=
  if lore.contains t then .fact else
  match (seen.find? (·.1 == t)).map (·.2) with
  | some "cite" => .citation | some "example" => .«example» | some "hedge" => .hedge
  | some "promise" | some "contribute" => .promise | some "define" => .fact
  | some "evaluate" => .fact
  | _ => if field (obj kinds t) "kind" == "fact" then .fact else .authors

def ruleOfJ (rj : Json) (concl : String) (prems : List String) (side : Side) (tagD : String → Tag) :
    Except String (Rule String) := do
  let some kind := (match str rj "kind" with | "strict" => some RKind.strict | "defeasible" => some .defeasible | _ => none)
    | throw s!"rule {str rj "id"}: kind must be strict or defeasible"
  let some sch := schemeOf (str rj "scheme") | throw s!"rule {str rj "id"}: unknown scheme {str rj "scheme"}"
  let tags := obj rj "tags"
  let premises ← prems.mapM fun p => do
    match (tags.getObjValAs? String p).toOption with
    | some s => match tagOf s with
      | some t => pure (p, t)
      | none => throw s!"rule {str rj "id"}: unknown tag {s}"
    | none => pure (p, tagD p)
  let roles := obj rj "roles"
  let slots ← prems.filterMapM fun p => do
    match (roles.getObjValAs? String p).toOption with
    | some s => match slotOfS s with
      | some sl => pure (some (p, sl))
      | none => throw s!"rule {str rj "id"}: unknown slot {s} (one of {", ".intercalate (allSlots.map slotS)})"
    | none => pure none
  pure { id := str rj "id", concl, premises, kind, scheme := sch, side,
         answered := nats rj "answered", pressed := nats rj "pressed", slots }

def rulesMain (dir : String) : IO Json := do
  let d := System.FilePath.mk dir
  let aj ← IO.ofExcept (Json.parse (← IO.FS.readFile (d / "argument.json")))
  let lore := strs aj "lore"
  let kinds := obj aj "terms"
  let pdir := d / "paragraphs"
  let names := ((← pdir.readDir).toList.filterMap fun f =>
    if f.fileName.endsWith ".argument.json" then some ((f.fileName.splitOn ".").head!) else none).mergeSort (· ≤ ·)
  let mut seen : List (String × String) := []
  let mut rules : Array (Rule String) := #[]
  let mut infos : Array Info := #[]
  let mut errs : Array String := #[]
  -- opponents first: positions the text argues against
  if let .ok (.arr os) := aj.getObjVal? "opponents" then
    for o in os do
      match ruleOfJ o (str o "concl") (strs o "premises") .opponent (fun p => tagFromMoves kinds lore [] p) with
      | .ok r =>
        rules := rules.push r
        infos := infos.push
          { id := r.id, para := str o "para", quote := str o "quote", quotes := obj o "quotes",
            notes := obj o "notes",
            attacks := match o.getObjVal? "attacks" with | .ok (.arr a) => a.toList | _ => [] }
      | .error e => errs := errs.push e
  for nm in names do
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (pdir / s!"{nm}.argument.json")))
    let .ok (.arr ms) := j.getObjVal? "moves" | continue
    for m in ms do
      let mv := str m "move"
      if mv == "infer" then
        if let .ok rj := m.getObjVal? "rule" then
          let s := seen
          match ruleOfJ rj (str m "t") (strs m "premises") .text (tagFromMoves kinds lore s) with
          | .ok r =>
            rules := rules.push r
            let atts := match rj.getObjVal? "attacks" with | .ok (.arr a) => a.toList | _ => []
            infos := infos.push
              { id := r.id, para := (if str rj "para" == "" then nm else str rj "para"), quote := str rj "quote", quotes := obj rj "quotes",
                notes := obj rj "notes", roles := obj rj "roles", attacks := atts }
          | .error e => errs := errs.push e
      let t := str m "t"
      if !(seen.any (·.1 == t)) && t != "" then seen := seen ++ [(t, mv)]
  let rs := rules.toList
  let as : List (RAttack String) := infos.toList.flatMap fun i => i.attacks.filterMap fun a =>
    (howOf (str a "how")).map fun how =>
      { src := i.id, tgt := str a "tgt", how, on := (a.getObjValAs? String "on").toOption }
  let lab := labels rs as
  let slab := scepticLabels rs as
  let get (l : List (String × Lab)) (x : String) := labS (((l.find? (·.1 == x)).map (·.2)).getD .undec)
  let ruleJ (r : Rule String) : Json :=
    let info := (infos.find? (·.id == r.id)).getD { id := r.id, para := "", quote := "", quotes := Json.mkObj [], notes := Json.mkObj [], attacks := [] }
    let quoteOf (t : String) := field info.quotes t
    let paraOf (t : String) := match info.quotes.getObjVal? t with
      | .ok (.obj _) => field (obj info.quotes t) "para" | _ => ""
    let qtext (t : String) := match info.quotes.getObjVal? t with
      | .ok (.obj _) => field (obj info.quotes t) "q" | _ => quoteOf t
    let gl (t : String) := field (obj kinds t) "gloss"
    Json.mkObj [
      ("id", r.id), ("concl", r.concl), ("gloss", gl r.concl), ("quote", info.quote), ("para", info.para),
      ("kind", match r.kind with | .strict => "strict" | .defeasible => "defeasible"),
      ("scheme", r.scheme.name), ("side", match r.side with | .text => "text" | .opponent => "opponent"),
      ("premises", Json.arr (r.premises.map fun (p, t) => Json.mkObj [
        ("t", p), ("tag", tagS t), ("quote", qtext p), ("gloss", gl p), ("para", paraOf p), ("role", match slotOf r p with | some sl => Json.str (slotS sl) | none => Json.str ""),
        ("sub", match concluder rs p with | some s => Json.str s.id | none => Json.null)]).toArray),
      ("cqs", Json.arr ((List.range r.scheme.cqs.length).map fun i =>
        let (q, how) := r.scheme.cqs.getD i ("", .undercut)
        Json.mkObj [("i", i), ("q", q), ("attack", howS how),
          ("status", if r.answered.contains i then "answered" else if r.pressed.contains i then "pressed" else "open"),
          ("note", field info.notes (toString i))]).toArray),
      ("label", get lab r.id), ("sceptic", get slab r.id),
      ("thin", toJson ((thin rs r).map thinS)), ("bare", bare rs r),
      ("faults", Json.arr ((faults r).map faultJ).toArray), ("enthymemes", toJson ((enthymemes r).map slotS))]
  let attJ := infos.toList.flatMap fun i => i.attacks.map fun a =>
    let ra : Option (RAttack String) := (howOf (str a "how")).map fun how =>
      { src := i.id, tgt := str a "tgt", how, on := (a.getObjValAs? String "on").toOption }
    Json.mkObj [("src", i.id), ("tgt", str a "tgt"), ("how", str a "how"),
      ("on", (a.getObjVal? "on").toOption.getD Json.null), ("quote", str a "quote"),
      ("ok", match ra with | some ra => attackOk rs ra | none => false),
      ("reaches", toJson (match ra with | some ra => if attackOk rs ra then reached rs ra.tgt else [] | none => []))]
  pure (Json.mkObj [
    ("root", str aj "root"),
    ("rules", Json.arr (rs.map ruleJ).toArray),
    ("attacks", Json.arr attJ.toArray),
    ("bare", toJson (bareRules rs)),
    ("bareLeaves", toJson (bareLeaves rs)),
    ("thin", Json.arr ((thinRules rs).map fun (i, ts) => Json.mkObj [("id", i), ("why", toJson (ts.map thinS))]).toArray),
    ("enthymemes", Json.arr ((enthymemeRules rs).map fun (i, ss) => Json.mkObj [("id", i), ("slots", toJson (ss.map slotS))]).toArray),
    ("shaped", decide (Shaped rs)),
    ("ok", decide (RulesOk rs as) && errs.isEmpty),
    ("errors", toJson errs.toList)])

/-- A story tag (studio/rules_story.py) as what the rule rests on. -/
def storyTag : String → Tag
  | "seen" | "check" => .fact | "told" => .citation | "belief" => .hedge
  | t => (tagOf t).getD .authors

/-- `langlib rules-json <file>`: a rules document built elsewhere (a story
adapter, a paper's unread inferences) in the shape `rulesMain` prints, checked
by World/Rules: each rule gets its labels, thin support, faults and enthymemes
recomputed, and the document whether it is well formed and well shaped. -/
def rulesJsonMain (file : String) : IO Json := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let rj := match j.getObjVal? "rules" with | .ok (.obj _) => (j.getObjVal? "rules").toOption.getD j | _ => j
  let rsJ := match rj.getObjVal? "rules" with | .ok (.arr a) => a.toList | _ => []
  let asJ := match rj.getObjVal? "attacks" with | .ok (.arr a) => a.toList | _ => []
  let mut errs : Array String := #[]
  let mut rs : Array (Rule String) := #[]
  for r in rsJ do
    let prem := match r.getObjVal? "premises" with | .ok (.arr a) => a.toList | _ => []
    let cqs := match r.getObjVal? "cqs" with | .ok (.arr a) => a.toList | _ => []
    let kind := if str r "kind" == "strict" then RKind.strict else .defeasible
    let sch := (schemeByName (str r "scheme")).getD .unread
    let mut slots : List (String × Slot) := []
    for p in prem do
      let role := str p "role"
      if role != "" then
        match slotOfS role with
        | some sl => slots := slots ++ [(str p "t", sl)]
        | none => errs := errs.push s!"rule {str r "id"}: unknown slot {role}"
    let st (c : Json) := str c "status"
    let ix (k : String) := (cqs.filter (st · == k)).filterMap fun c => (c.getObjValAs? Nat "i").toOption
    let rule : Rule String :=
      { id := str r "id", concl := str r "concl", kind, scheme := sch,
        side := if str r "side" == "opponent" then .opponent else .text,
        premises := prem.map fun p => (str p "t", storyTag (str p "tag")),
        answered := ix "answered", pressed := ix "pressed", slots }
    rs := rs.push rule
  let rl := rs.toList
  let as : List (RAttack String) := asJ.filterMap fun a => (howOf (str a "how")).map fun how =>
    { src := str a "src", tgt := str a "tgt", how, on := (a.getObjValAs? String "on").toOption }
  let lab := labels rl as
  let slab := scepticLabels rl as
  let get (l : List (String × Lab)) (x : String) := labS (((l.find? (·.1 == x)).map (·.2)).getD .undec)
  let rules := rsJ.zip rl |>.map fun (rj, r) =>
    let rj := (((((rj.setObjVal! "label" (get lab r.id)).setObjVal! "sceptic" (get slab r.id)).setObjVal! "thin"
      (toJson ((thin rl r).map thinS))).setObjVal! "bare" (bare rl r)).setObjVal! "faults"
      (Json.arr ((faults r).map faultJ).toArray)).setObjVal! "enthymemes" (toJson ((enthymemes r).map slotS))
    rj.setObjVal! "premises" (Json.arr ((match rj.getObjVal? "premises" with | .ok (.arr a) => a.toList | _ => []).map fun (p : Json) =>
      p.setObjVal! "sub" (match concluder rl (str p "t") with | some s => Json.str s.id | none => Json.null)).toArray)
  let atts := asJ.map fun a =>
    let ra : Option (RAttack String) := (howOf (str a "how")).map fun how =>
      { src := str a "src", tgt := str a "tgt", how, on := (a.getObjValAs? String "on").toOption }
    (a.setObjVal! "ok" (match ra with | some ra => attackOk rl ra | none => false)).setObjVal! "reaches"
      (toJson (match ra with | some ra => if attackOk rl ra then reached rl ra.tgt else [] | none => []))
  let out := ((((((((rj.setObjVal! "rules" (Json.arr rules.toArray)).setObjVal! "attacks" (Json.arr atts.toArray)).setObjVal!
    "bare" (toJson (bareRules rl))).setObjVal! "bareLeaves" (toJson (bareLeaves rl))).setObjVal! "thin"
    (Json.arr ((thinRules rl).map fun (i, ts) => Json.mkObj [("id", i), ("why", toJson (ts.map thinS))]).toArray)).setObjVal!
    "enthymemes" (Json.arr ((enthymemeRules rl).map fun (i, ss) => Json.mkObj [("id", i), ("slots", toJson (ss.map slotS))]).toArray)).setObjVal!
    "shaped" (decide (Shaped rl))).setObjVal! "ok" (decide (RulesOk rl as) && errs.isEmpty)).setObjVal! "errors" (toJson errs.toList)
  pure (match j.getObjVal? "rules" with | .ok (.obj _) => j.setObjVal! "rules" out | _ => out)

end LangLib.Studio.RulesView
