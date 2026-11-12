import Lean.Data.Json
import LangLib.Basic

/-!
# JSON format

A compact format meant to be written by an LLM:

```json
{ "entities": [{"id": "kiran", "name": "Kiran", "kind": "person", "pron": "she"}],
  "topics":   [{"id": "t1", "label": "the interview", "entities": ["kiran"]}],
  "sentences": [
    {"c": "S", "topic": "t1", "k": [
      {"w": "She", "p": "PRON", "r": "nsubj", "ref": "kiran"},
      {"c": "VP", "r": "head", "k": [{"w": "laughed", "p": "VERB", "r": "head", "l": "laugh"}]},
      {"w": ".", "p": "PUNCT", "r": "punct"}]}]}
```

A leaf has `w` (the token) and `p` (UPOS); a node has `c` (category) and `k`
(children). Optional: `r` role, `l` lemma, `f` features object, `ref` entity,
`spk` speaker (on QUOTE nodes), `topic` (on a sentence root).
Errors carry a JSON path such as `sentences[3].k[0].k[2]`.
-/

namespace LangLib
open Lean

private def optStr (j : Json) (k : String) : Option String :=
  (j.getObjValAs? String k).toOption

private def enumField {α} (path k : String) (parse : String → Option α)
    (j : Json) : Except String (Option α) :=
  match j.getObjVal? k with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .ok s => match parse s with
      | some a => pure (some a)
      | none => throw s!"{path}: unknown {k} \"{s}\""
    | .error _ => throw s!"{path}: field {k} must be a string"

partial def treeOfJson (path : String) (j : Json) : Except String Tree := do
  let role ← enumField path "r" Role.ofString? j
  let ref := optStr j "ref"
  match j.getObjVal? "w" with
  | .ok wv =>
    let form ← match wv.getStr? with
      | .ok s => pure s
      | .error _ => throw s!"{path}: w must be a string"
    let some upos ← enumField path "p" UPOS.ofString? j
      | throw s!"{path}: leaf \"{form}\" is missing p (part of speech)"
    let feats : List (String × String) :=
      match j.getObjVal? "f" with
      | .ok (.obj kvs) => kvs.toList.filterMap fun (k, v) =>
          match v.getStr? with | .ok s => some (k, s) | .error _ => none
      | _ => []
    pure (.leaf { form, upos, role, lemma := optStr j "l", feats, ref })
  | .error _ =>
    let some cat ← enumField path "c" Cat.ofString? j
      | throw s!"{path}: object is neither a leaf (w) nor a node (c)"
    let kidsJ ← match j.getObjVal? "k" with
      | .ok (.arr a) => pure a
      | _ => throw s!"{path}: node {cat.name} needs a k array of children"
    let mut kids := #[]
    for h : i in [0:kidsJ.size] do
      kids := kids.push (← treeOfJson s!"{path}.k[{i}]" kidsJ[i])
    pure (.node { cat, role, ref, speaker := optStr j "spk" } kids.toList)

def entityOfJson (path : String) (j : Json) : Except String Entity := do
  let some id := optStr j "id" | throw s!"{path}: entity needs id"
  let kind ← enumField path "kind" EntityKind.ofString? j
  let pron ← enumField path "pron" PronSeries.ofString? j
  pure { id, name := (optStr j "name").getD id, kind := kind.getD .person, pron }

def topicOfJson (path : String) (j : Json) : Except String Topic := do
  let some id := optStr j "id" | throw s!"{path}: topic needs id"
  let entities := match j.getObjValAs? (Array String) "entities" with
    | .ok a => a.toList | .error _ => []
  pure { id, label := (optStr j "label").getD id, entities }

private def arrField (j : Json) (k : String) : Array Json :=
  match j.getObjVal? k with | .ok (.arr a) => a | _ => #[]

def docOfJson (j : Json) : Except String Doc := do
  let es := arrField j "entities"
  let ts := arrField j "topics"
  let ss := arrField j "sentences"
  let mut entities := #[]
  for h : i in [0:es.size] do
    entities := entities.push (← entityOfJson s!"entities[{i}]" es[i])
  let mut topics := #[]
  for h : i in [0:ts.size] do
    topics := topics.push (← topicOfJson s!"topics[{i}]" ts[i])
  let mut sentences := #[]
  for h : i in [0:ss.size] do
    let tree ← treeOfJson s!"sentences[{i}]" ss[i]
    sentences := sentences.push { tree, topic := optStr ss[i] "topic" }
  pure { entities := entities.toList, topics := topics.toList,
         sentences := sentences.toList }

def docOfString (s : String) : Except String Doc := do
  docOfJson (← Json.parse s)

/-! Serialisation back to the same format. -/

private def withOpt (fs : List (String × Json)) (k : String) : Option String → List (String × Json)
  | some v => fs ++ [(k, Json.str v)]
  | none => fs

partial def Tree.toJson : Tree → Json
  | .leaf w =>
    let fs : List (String × Json) := [("w", w.form), ("p", w.upos.name)]
    let fs := withOpt fs "r" (w.role.map Role.name)
    let fs := withOpt fs "l" w.lemma
    let fs := if w.feats.isEmpty then fs else
      fs ++ [("f", Json.mkObj (w.feats.map fun (k, v) => (k, Json.str v)))]
    Json.mkObj (withOpt fs "ref" w.ref)
  | .node i kids =>
    let fs : List (String × Json) := [("c", i.cat.name)]
    let fs := withOpt fs "r" (i.role.map Role.name)
    let fs := withOpt fs "ref" i.ref
    let fs := withOpt fs "spk" i.speaker
    Json.mkObj (fs ++ [("k", Json.arr (kids.map Tree.toJson).toArray)])

def Doc.toJson (d : Doc) : Json :=
  Json.mkObj [
    ("entities", Json.arr (d.entities.map fun e =>
      Json.mkObj ([("id", Json.str e.id), ("name", Json.str e.name),
                   ("kind", Json.str e.kind.name)] ++
                  (e.pron.map fun p => [("pron", Json.str p.name)]).getD [])).toArray),
    ("topics", Json.arr (d.topics.map fun t =>
      Json.mkObj [("id", t.id), ("label", t.label),
                  ("entities", Json.arr (t.entities.map Json.str).toArray)]).toArray),
    ("sentences", Json.arr (d.sentences.map fun s =>
      match s.topic, s.tree.toJson with
      | some t, .obj kvs => .obj (kvs.insert "topic" (Json.str t))
      | _, j => j).toArray)]

end LangLib
