import Lean.Data.Json
import Std.Data.HashMap
import LangLib.Basic
import LangLib.Render

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

/-! ## Flat format

The same document without nesting: every word and every phrase names its
parent phrase with `in`; phrases without `in` are sentence roots. Children are
ordered by their first word, so a phrase whose words are not contiguous renders
out of order and fails the token check.

```json
{ "entities": [...], "topics": [...],
  "nodes": [{"id": "s1", "c": "S", "r": "root", "topic": "t1"},
            {"id": "np1", "c": "NP", "r": "nsubj", "ref": "kiran", "in": "s1"}],
  "words": [{"w": "She", "p": "PRON", "r": "head", "in": "np1"},
            {"w": "laughed", "p": "VERB", "r": "head", "in": "s1"},
            {"w": ".", "p": "PUNCT", "r": "punct", "in": "s1"}] }
```
-/

private inductive Item | word (i : Nat) | node (id : String)

def docOfFlat (j : Json) : Except String Doc := do
  let es := arrField j "entities"
  let ts := arrField j "topics"
  let mut entities := #[]
  for h : i in [0:es.size] do
    entities := entities.push (← entityOfJson s!"entities[{i}]" es[i])
  let mut topics := #[]
  for h : i in [0:ts.size] do
    topics := topics.push (← topicOfJson s!"topics[{i}]" ts[i])
  let wsJ := arrField j "words"
  let nsJ := arrField j "nodes"
  let mut leaves : Array Tree := #[]
  let mut items : Array (String × Item) := #[]
  for h : i in [0:wsJ.size] do
    let t ← treeOfJson s!"words[{i}]" wsJ[i]
    let some p := optStr wsJ[i] "in" | throw s!"words[{i}] (\"{(t.render.headD "")}\") needs in (its parent node id)"
    leaves := leaves.push t
    items := items.push (p, .word i)
  let mut infos : Std.HashMap String (NodeInfo × Option String) := {}
  let mut roots : Array String := #[]
  for h : i in [0:nsJ.size] do
    let n := nsJ[i]
    let path := s!"nodes[{i}]"
    let some id := optStr n "id" | throw s!"{path}: node needs id"
    if infos.contains id then throw s!"{path}: duplicate node id \"{id}\""
    let some cat ← enumField path "c" Cat.ofString? n | throw s!"{path}: node needs c"
    let role ← enumField path "r" Role.ofString? n
    infos := infos.insert id ({ cat, role, ref := optStr n "ref", speaker := optStr n "spk" },
                              optStr n "topic")
    match optStr n "in" with
    | some p => items := items.push (p, .node id)
    | none => roots := roots.push id
  for (p, _) in items do
    if !infos.contains p then throw s!"parent \"{p}\" is not a declared node id"
  let budget := nsJ.size + 1
  -- build a node's subtree; returns it with the index of its first word
  let rec build (fuel : Nat) (id : String) : Except String (Tree × Nat) := do
    match fuel with
    | 0 => throw s!"node \"{id}\" is part of a cycle"
    | fuel + 1 =>
      let mut kids : Array (Tree × Nat) := #[]
      for (p, it) in items do
        if p == id then
          match it with
          | .word i => kids := kids.push (leaves[i]!, i)
          | .node c => kids := kids.push (← build fuel c)
      if kids.isEmpty then throw s!"node \"{id}\" has no children"
      let sorted := kids.toList.mergeSort (fun a b => a.2 ≤ b.2)
      let (info, _) := infos.getD id default
      pure (.node info (sorted.map (·.1)), (sorted.headD (default, 0)).2)
  let mut sents : Array (Sentence × Nat) := #[]
  for r in roots do
    let (t, m) ← build budget r
    sents := sents.push ({ tree := t, topic := (infos.getD r default).2 }, m)
  let built := (sents.toList.map (·.1.tree.leaves.length)).sum
  if built != wsJ.size then
    throw s!"only {built} of {wsJ.size} words hang under a root; check the in links for cycles"
  pure { entities := entities.toList, topics := topics.toList,
         sentences := (sents.toList.mergeSort (fun a b => a.2 ≤ b.2)).map (·.1) }

def docOfString (s : String) : Except String Doc := do
  let j ← Json.parse s
  if (j.getObjVal? "words").isOk then docOfFlat j else docOfJson j

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
