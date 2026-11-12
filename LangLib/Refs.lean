import LangLib.Basic
import LangLib.Render

/-!
# References

Collects every mention (a word or constituent carrying `ref`) with its token
position, then checks the reference layer:

* every `ref`, `spk` and topic entity is declared;
* a third-person pronoun agrees with its entity's pronoun series;
* a third-person pronoun that is not an expletive has a referent.

Each pronoun mention is classified by where its entity's full mentions are:
anaphoric (one comes earlier), cataphoric (only later ones), or unanchored
(none, e.g. a narrator only ever called "I").
-/

namespace LangLib

inductive MentionKind where
  | pronoun | full
  deriving Repr, DecidableEq

structure Mention where
  entity : EntityId
  /-- index of the mention's first token in the document -/
  pos : Nat
  text : String
  kind : MentionKind
  deriving Repr

/-- Third-person pronoun forms and their series. -/
def thirdPersonSeries (form : String) : Option PronSeries :=
  match form.toLower with
  | "he" | "him" | "his" | "himself" => some .he
  | "she" | "her" | "hers" | "herself" => some .she
  | "it" | "its" | "itself" => some .it
  | "they" | "them" | "their" | "theirs" | "themselves" | "themself" => some .they
  | _ => none

private def contentLeaves (t : Tree) : List Word :=
  t.leaves.filter (·.upos != .PUNCT)

private def isPronounMention (t : Tree) : Bool :=
  match contentLeaves t with
  | [w] => w.upos == .PRON
  | _ => false

/-- Mentions in document order. -/
partial def Tree.mentions (t : Tree) (start : Nat) : List Mention × Nat :=
  match t with
  | .leaf w =>
    let ms := match w.ref with
      | some e => [{ entity := e, pos := start, text := w.form,
                     kind := if w.upos == .PRON then .pronoun else .full : Mention }]
      | none => []
    (ms, start + 1)
  | .node i kids =>
    let here := match i.ref with
      | some e => [{ entity := e, pos := start, text := " ".intercalate t.render,
                     kind := if isPronounMention t then .pronoun else .full : Mention }]
      | none => []
    let (inner, stop) := kids.foldl (fun (acc, p) k =>
      let (ms, p') := k.mentions p
      (acc ++ ms, p')) (([] : List Mention), start)
    (here ++ inner, stop)

def Doc.mentions (d : Doc) : List Mention :=
  (d.sentences.foldl (fun (acc, p) s =>
    let (ms, p') := s.tree.mentions p
    (acc ++ ms, p')) (([] : List Mention), 0)).1

/-- Positions of pronoun leaves, with the word. -/
def Doc.pronounLeaves (d : Doc) : List (Nat × Word) :=
  ((d.sentences.flatMap (·.tree.leaves)).zipIdx).filterMap fun (w, i) =>
    if w.upos == .PRON then some (i, w) else none

partial def Tree.speakers : Tree → List EntityId
  | .leaf _ => []
  | .node i kids => i.speaker.toList ++ kids.flatMap Tree.speakers

inductive RefIssue where
  | duplicateEntity (id : EntityId)
  | unknownEntity (id : EntityId) (pos : Nat) (text : String)
  | unknownTopic (id : String)
  | disagreement (pos : Nat) (form : String) (entity : EntityId) (expected : PronSeries)
  | unresolvedPronoun (pos : Nat) (form : String)
  deriving Repr

def RefIssue.describe : RefIssue → String
  | .duplicateEntity id => s!"entity \"{id}\" is declared twice"
  | .unknownEntity id p t => s!"\"{t}\" (token {p}) refers to undeclared entity \"{id}\""
  | .unknownTopic id => s!"topic \"{id}\" is used but not declared"
  | .disagreement p f e s =>
    s!"pronoun \"{f}\" (token {p}) refers to \"{e}\", whose pronouns are {s.name}"
  | .unresolvedPronoun p f =>
    s!"pronoun \"{f}\" (token {p}) has no ref; give it (or its NP) a ref, or role expl"

inductive Phora where
  | anaphoric | cataphoric | unanchored
  deriving Repr, DecidableEq

def Phora.name : Phora → String
  | .anaphoric => "anaphoric" | .cataphoric => "cataphoric" | .unanchored => "unanchored"

structure RefReport where
  issues : List RefIssue
  /-- each pronoun mention with its classification -/
  pronouns : List (Mention × Phora)
  mentions : Nat

def Doc.checkRefs (d : Doc) : RefReport := Id.run do
  let ids := d.entities.map (·.id)
  let mut issues : Array RefIssue := #[]
  let mut seen : List EntityId := []
  for id in ids do
    if seen.contains id then issues := issues.push (.duplicateEntity id)
    seen := id :: seen
  let ms := d.mentions
  for m in ms do
    if !ids.contains m.entity then
      issues := issues.push (.unknownEntity m.entity m.pos m.text)
  for s in d.sentences do
    for e in s.tree.speakers do
      if !ids.contains e then issues := issues.push (.unknownEntity e 0 "speaker")
    if let some t := s.topic then
      if !(d.topics.map (·.id)).contains t then issues := issues.push (.unknownTopic t)
  for t in d.topics do
    for e in t.entities do
      if !ids.contains e then issues := issues.push (.unknownEntity e 0 s!"topic {t.id}")
  -- agreement
  for m in ms do
    if m.kind == .pronoun then
      if let some got := thirdPersonSeries m.text then
        if let some ent := d.entities.find? (·.id == m.entity) then
          if let some want := ent.pron then
            if got != want then
              issues := issues.push (.disagreement m.pos m.text m.entity want)
  -- unresolved third-person pronouns
  let covered := (ms.filter (·.kind == .pronoun)).map (·.pos)
  for (p, w) in d.pronounLeaves do
    if (thirdPersonSeries w.form).isSome && !covered.contains p && w.role != some .expl then
      issues := issues.push (.unresolvedPronoun p w.form)
  -- anaphora / cataphora
  let pron := ms.filter (·.kind == .pronoun)
  let classified := pron.map fun m =>
    let fulls := ms.filter fun n => n.entity == m.entity && n.kind == .full
    let ph :=
      if fulls.any (·.pos < m.pos) then Phora.anaphoric
      else if fulls.any (·.pos > m.pos) then .cataphoric
      else .unanchored
    (m, ph)
  return { issues := issues.toList, pronouns := classified, mentions := ms.length }

end LangLib
