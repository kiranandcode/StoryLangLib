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

An `infer` move carries its rule in a `rule` field:

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
  pure { id := str rj "id", concl, premises, kind, scheme := sch, side,
         answered := nats rj "answered", pressed := nats rj "pressed" }

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
                notes := obj rj "notes", attacks := atts }
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
    Json.mkObj [
      ("id", r.id), ("concl", r.concl), ("quote", info.quote), ("para", info.para),
      ("kind", match r.kind with | .strict => "strict" | .defeasible => "defeasible"),
      ("scheme", r.scheme.name), ("side", match r.side with | .text => "text" | .opponent => "opponent"),
      ("premises", Json.arr (r.premises.map fun (p, t) => Json.mkObj [
        ("t", p), ("tag", tagS t), ("quote", qtext p), ("para", paraOf p),
        ("sub", match concluder rs p with | some s => Json.str s.id | none => Json.null)]).toArray),
      ("cqs", Json.arr ((List.range r.scheme.cqs.length).map fun i =>
        let (q, how) := r.scheme.cqs.getD i ("", .undercut)
        Json.mkObj [("i", i), ("q", q), ("attack", howS how),
          ("status", if r.answered.contains i then "answered" else if r.pressed.contains i then "pressed" else "open"),
          ("note", field info.notes (toString i))]).toArray),
      ("label", get lab r.id), ("sceptic", get slab r.id),
      ("thin", toJson ((thin rs r).map thinS)), ("bare", bare rs r)]
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
    ("ok", decide (RulesOk rs as) && errs.isEmpty),
    ("errors", toJson errs.toList)])

end LangLib.Studio.RulesView
