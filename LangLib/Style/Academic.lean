import Lean.Data.Json
import LangLib.Json
import LangLib.Style.Core

/-!
# Academic style: information flow over checked trees

Kiran's principles for papers (`~/Documents/code/prompts/writing-style.md`) and
the structurally visible LLM-isms (`llmisms.md`) as decidable rules. The design
follows `Core.lean`: `asentOf` reads each sentence tree once into a flat record
(`ASent`, run by the CLI), and every feature is structural recursion over
`List ASent`, so `langlib academic <dir> --lean <name>` prints records that a
theorem file restates and judges by `decide +kernel`.

What a record keeps: the entities the sentence mentions, each with the word
index of its first mention (every `ref` on a node or leaf); the entity of the
main clause's subject (`nsubj`, found down the chain of heads) and where it
starts; whether the sentence is a run-in heading (`FRAG` root); and counts of
em-dashes, colon setups and "not X but Y" antitheses, and whether it is, or
sets up, a question.

The rules, over the whole excerpt in reading order:

* **old to new**: a sentence's subject is *given* (a discourse participant,
  the authors or the reader, or an entity already mentioned) and the entities
  it introduces come after the subject, in the predicate;
* **first sentence summarises**: in each paragraph of two or more sentences,
  the first (non-heading) sentence mentions the entity the most sentences of
  the paragraph mention;
* **just in time**: an entity that is used again is used again within three
  sentences of its introduction;
* **callbacks**: a mention of an entity after a gap of at least six sentences
  and in a later paragraph;
* **question then answer**: a sentence that asks or sets up a question (ends
  in "?", or uses "wonder"/"question") is followed by a sentence that is not a
  question and shares an entity with it;
* **LLM-isms**: em-dashes, colons as setup (a colon followed by more words,
  not a list, not "::", not a heading), "not X but Y" (a negation, not "not
  only", followed in the same sentence by "but", "rather", "instead" or ";"),
  rhetorical questions ("?" left unanswered by the rule above).
-/

namespace LangLib.Style.Academic
open LangLib

/-! ## Per sentence -/

structure ASent where
  para : Nat := 0
  words : Nat := 0
  /-- a run-in heading or other non-clause (`FRAG` root) -/
  heading : Bool := false
  /-- the entity the main clause's subject mentions -/
  subj : Option String := none
  /-- word index where the subject starts -/
  subjAt : Nat := 0
  /-- entities mentioned, each once, with the word index of its first mention -/
  ents : List (String × Nat) := []
  /-- ends in "?" -/
  question : Bool := false
  /-- asks or sets up a question ("?", "wonder", "question") -/
  asks : Bool := false
  dashes : Nat := 0
  colonSetups : Nat := 0
  antithesis : Nat := 0
  deriving Repr, DecidableEq, Inhabited

private def lower (s : String) : String := s.toLower
private def isWord (w : Word) : Bool := w.upos != .PUNCT && w.upos != .SYM

private def roleIs (t : Tree) (r : Role) : Bool := match t with
  | .leaf w => w.role == some r
  | .node i _ => i.role == some r

private partial def leavesOf : Tree → List Word
  | .leaf w => [w]
  | .node _ kids => kids.flatMap leavesOf

private def wc (t : Tree) : Nat := ((leavesOf t).filter isWord).length

/-- The entity a constituent mentions. -/
private partial def refOf : Tree → Option String
  | .leaf w => w.ref
  | .node i kids => i.ref <|> kids.findSome? fun k => match k with
    | .leaf w => if w.role == some .head then w.ref else none
    | .node j _ => if j.cat == .NP || j.role == some .head then refOf k else none

/-- Every mention, in reading order, with the word index where it starts. -/
private partial def mentions : Tree → Nat → List (String × Nat) × Nat
  | .leaf w, i => ((w.ref.map fun r => [(r, i)]).getD [], if isWord w then i + 1 else i)
  | .node info kids, i =>
    let own := (info.ref.map fun r => [(r, i)]).getD []
    kids.foldl (fun (acc, j) k => let (m, j') := mentions k j; (acc ++ m, j')) (own, i)

private def firstEach (ms : List (String × Nat)) : List (String × Nat) :=
  ms.foldl (fun acc (e, i) => if acc.any (·.1 == e) then acc else acc ++ [(e, i)]) []

/-- The main clause's subject: an `nsubj` child, else down the heads. -/
private partial def mainSubj (t : Tree) (start : Nat) : Option (Option String × Nat) :=
  match t with
  | .leaf _ => none
  | .node _ kids =>
    let starts := (kids.foldl (fun (acc, j) k => (acc ++ [(k, j)], j + wc k)) ([], start)).1
    match starts.find? (fun (k, _) => roleIs k .nsubj) with
    | some (k, j) => some (refOf k, j)
    | none => starts.findSome? fun (k, j) => match k with
      | .node info _ =>
        if info.role == some .head || (info.cat == .S &&
            (info.role.isNone || info.role == some .conj || info.role == some .root))
        then mainSubj k j else none
      | _ => none

def negations : List String := ["not", "never", "no"]
def turns : List String := ["but", "rather", "instead", ";"]

/-- "not X but Y": a negation (not "not only") with a turn after it. -/
partial def antithesisIn : List String → Nat
  | [] => 0
  | f :: rest =>
    let neg := (negations.contains f || f.endsWith "n't") && rest.head? != some "only"
    if neg && rest.any turns.contains then 1 + antithesisIn (rest.dropWhile (!turns.contains ·))
    else antithesisIn rest

/-- Colons that set something up: more words follow, not a list, not "::". -/
def colonSetupsIn (ws : List Word) : Nat :=
  let arr := ws.toArray
  (List.range arr.size).foldl (fun n k =>
    let w := arr[k]!
    if w.form != ":" then n else
    let prev := if k == 0 then "" else arr[k - 1]!.form
    let next? := arr[k + 1]?
    match next? with
    | none => n
    | some nx =>
      if prev == ":" || nx.form == ":" || nx.form == "(" || nx.form == "•" || nx.upos == .NUM ||
         !(arr.toList.drop (k + 1)).any isWord then n else n + 1) 0

def asentOf (para : Nat) (t : Tree) : ASent :=
  let ls := leavesOf t
  let forms := ls.map (lower ·.form)
  let heading := match t with | .node i _ => i.cat == .FRAG | .leaf _ => true
  let (ms, _) := mentions t 0
  let subj := mainSubj t 0
  let question := (ls.filter (·.upos == .PUNCT)).getLast?.map (·.form == "?") |>.getD false
  { para, words := (ls.filter isWord).length, heading,
    subj := subj.bind (·.1), subjAt := (subj.map (·.2)).getD 0,
    ents := firstEach ms, question,
    asks := question || forms.any (["wonder", "wonders", "question"].contains ·),
    dashes := (forms.filter (fun f => f == "—" || f == "--")).length,
    colonSetups := if heading then 0 else colonSetupsIn ls,
    antithesis := antithesisIn forms }

def asentsOfDoc (para : Nat) (d : Doc) : List ASent := d.sentences.map fun s => asentOf para s.tree

/-! ## Features (structural, kernel-friendly) -/

/-- The authors and the reader are given by the situation. -/
def given : List String := ["authors", "reader"]

def names (s : ASent) : List String := s.ents.map (·.1)

structure Flow where
  /-- sentences (not the first, not headings) with a tracked subject -/
  tracked : Nat := 0
  /-- of those, subjects that are given -/
  oldSubj : Nat := 0
  /-- entities first mentioned in such sentences -/
  newEnts : Nat := 0
  /-- of those, mentioned after the subject starts -/
  newLate : Nat := 0
  deriving Repr, DecidableEq

def flowFrom : List String → List ASent → Flow
  | _, [] => {}
  | seen, s :: ss =>
    let r := flowFrom (seen ++ names s) ss
    if s.heading || seen.isEmpty then r else
    match s.subj with
    | none => r
    | some e =>
      let news := s.ents.filter fun (x, _) => !given.contains x && !seen.contains x
      { tracked := r.tracked + 1,
        oldSubj := r.oldSubj + (if given.contains e || seen.contains e then 1 else 0),
        newEnts := r.newEnts + news.length,
        newLate := r.newLate + (news.filter (·.2 > s.subjAt)).length }

def groupParas : List ASent → List (List ASent)
  | [] => []
  | s :: ss => match groupParas ss with
    | (t :: ts) :: rest => if t.para == s.para then (s :: t :: ts) :: rest else [s] :: (t :: ts) :: rest
    | rest => [s] :: rest

def countMentions (e : String) : List ASent → Nat
  | [] => 0
  | s :: ss => (if (names s).contains e then 1 else 0) + countMentions e ss

def distinct : List String → List String
  | [] => []
  | x :: xs => let r := distinct xs; if r.contains x then r else x :: r

/-- The first non-heading sentence mentions an entity no other entity outnumbers. -/
def summarises (ps : List ASent) : Bool :=
  let body := ps.filter (!·.heading)
  match body with
  | [] => true
  | first :: _ =>
    let es := (distinct (body.flatMap names)).filter (!given.contains ·)
    let top := es.foldl (fun m e => max m (countMentions e body)) 0
    (names first).any fun e => !given.contains e && countMentions e body == top

def multi (ps : List ASent) : Bool := (ps.filter (!·.heading)).length ≥ 2

/-- Sentence indices mentioning `e`. -/
def positions (e : String) (ss : List ASent) : List (Nat × Nat) :=
  (ss.zipIdx.filter fun (s, _) => (names s).contains e).map fun (s, i) => (i, s.para)

def gapsOf : List (Nat × Nat) → List ((Nat × Nat) × (Nat × Nat))
  | a :: b :: rest => (a, b) :: gapsOf (b :: rest)
  | _ => []

def isCallback (p : (Nat × Nat) × (Nat × Nat)) : Bool := p.2.1 ≥ p.1.1 + 6 && p.2.2 != p.1.2

/-- A sentence that asks is answered by the next one: not a question, and sharing an entity. -/
def answeredAt : List ASent → List Bool
  | [] => []
  | [s] => if s.asks then [false] else []
  | s :: t :: rest =>
    (if s.asks then
      [!t.question && (names s).any fun e => !given.contains e && (names t).contains e]
     else []) ++ answeredAt (t :: rest)

def rhetoricalIn : List ASent → Nat
  | [] => 0
  | [s] => if s.question then 1 else 0
  | s :: t :: rest =>
    (if s.question && !(!t.question && (names s).any fun e => !given.contains e && (names t).contains e)
     then 1 else 0) + rhetoricalIn (t :: rest)

def sumBy (f : ASent → Nat) : List ASent → Nat
  | [] => 0
  | s :: ss => f s + sumBy f ss

structure AFeatures where
  sents : Nat
  words : Nat
  paras : Nat
  multiParas : Nat
  firstSum : Nat
  tracked : Nat
  oldSubj : Nat
  newEnts : Nat
  newLate : Nat
  /-- entities mentioned in at least two sentences -/
  reused : Nat
  /-- of those, used again within three sentences of their introduction -/
  jit : Nat
  callbacks : Nat
  asks : Nat
  answered : Nat
  questions : Nat
  rhetorical : Nat
  dashes : Nat
  colonSetups : Nat
  antithesis : Nat
  deriving Repr, DecidableEq, Inhabited

def AFeatures.ofSents (ss : List ASent) : AFeatures :=
  let fl := flowFrom [] ss
  let ps := groupParas ss
  let es := (distinct (ss.flatMap names)).filter (!given.contains ·)
  let poss := es.map (positions · ss)
  let reused := poss.filter (·.length ≥ 2)
  let ans := answeredAt ss
  { sents := ss.length, words := sumBy (·.words) ss, paras := ps.length,
    multiParas := (ps.filter multi).length,
    firstSum := (ps.filter fun p => multi p && summarises p).length,
    tracked := fl.tracked, oldSubj := fl.oldSubj, newEnts := fl.newEnts, newLate := fl.newLate,
    reused := reused.length,
    jit := (reused.filter fun p => match p with
      | a :: b :: _ => b.1 ≤ a.1 + 3 | _ => false).length,
    callbacks := (poss.flatMap fun p => (gapsOf p).filter isCallback).length,
    asks := ans.length, answered := (ans.filter id).length,
    questions := (ss.filter (·.question)).length, rhetorical := rhetoricalIn ss,
    dashes := sumBy (·.dashes) ss, colonSetups := sumBy (·.colonSetups) ss,
    antithesis := sumBy (·.antithesis) ss }

inductive AFeat where
  | sents | words | paras | multiParas | firstSum | tracked | oldSubj | newEnts | newLate
  | reused | jit | callbacks | asks | answered | unanswered | questions | rhetorical
  | dashes | colonSetups | antithesis
  deriving Repr, DecidableEq, Inhabited

def AFeatures.get (f : AFeatures) : AFeat → Nat
  | .sents => f.sents | .words => f.words | .paras => f.paras | .multiParas => f.multiParas
  | .firstSum => f.firstSum | .tracked => f.tracked | .oldSubj => f.oldSubj
  | .newEnts => f.newEnts | .newLate => f.newLate | .reused => f.reused | .jit => f.jit
  | .callbacks => f.callbacks | .asks => f.asks | .answered => f.answered
  | .unanswered => f.asks - f.answered | .questions => f.questions
  | .rhetorical => f.rhetorical | .dashes => f.dashes | .colonSetups => f.colonSetups
  | .antithesis => f.antithesis

def AFeat.name : AFeat → String
  | .sents => "sents" | .words => "words" | .paras => "paras" | .multiParas => "multiParas"
  | .firstSum => "firstSum" | .tracked => "tracked" | .oldSubj => "oldSubj"
  | .newEnts => "newEnts" | .newLate => "newLate" | .reused => "reused" | .jit => "jit"
  | .callbacks => "callbacks" | .asks => "asks" | .answered => "answered"
  | .unanswered => "unanswered" | .questions => "questions" | .rhetorical => "rhetorical"
  | .dashes => "dashes" | .colonSetups => "colonSetups" | .antithesis => "antithesis"

def AFeat.all : List AFeat :=
  [.sents, .words, .paras, .multiParas, .firstSum, .tracked, .oldSubj, .newEnts, .newLate,
   .reused, .jit, .callbacks, .asks, .answered, .unanswered, .questions, .rhetorical,
   .dashes, .colonSetups, .antithesis]

/-! ## Rules and styles -/

inductive ARule where
  | atLeast (f : AFeat) (n : Nat)
  | atMost (f : AFeat) (n : Nat)
  /-- `num / den ≥ p / q` -/
  | ratioAtLeast (num den : AFeat) (p q : Nat)
  /-- `num / den ≤ p / q` -/
  | ratioAtMost (num den : AFeat) (p q : Nat)
  deriving Repr, DecidableEq, Inhabited

def ARule.holds (f : AFeatures) : ARule → Bool
  | .atLeast x n => f.get x ≥ n
  | .atMost x n => f.get x ≤ n
  | .ratioAtLeast a b p q => f.get a * q ≥ p * f.get b
  | .ratioAtMost a b p q => f.get a * q ≤ p * f.get b

def ARule.show : ARule → String
  | .atLeast x n => s!"{x.name} ≥ {n}"
  | .atMost x n => s!"{x.name} ≤ {n}"
  | .ratioAtLeast a b p q => s!"{a.name} / {b.name} ≥ {p}/{q}"
  | .ratioAtMost a b p q => s!"{a.name} / {b.name} ≤ {p}/{q}"

structure AStyle where
  name : String
  rules : List (String × ARule)

def AStyle.failing (st : AStyle) (f : AFeatures) : List String :=
  (st.rules.filter fun (_, r) => !r.holds f).map (·.1)

def AStyle.holds (st : AStyle) (f : AFeatures) : Bool := (st.failing f).isEmpty

/-- Kiran's principles for papers (thresholds are judgement calls, not
measurements of her writing). -/
def kiran : AStyle where
  name := "kiran"
  rules := [
    ("old to new: subjects given", .ratioAtLeast .oldSubj .tracked 3 4),
    ("old to new: new comes late", .ratioAtLeast .newLate .newEnts 2 3),
    ("first sentence summarises", .ratioAtLeast .firstSum .multiParas 2 3),
    ("just in time", .ratioAtLeast .jit .reused 1 2),
    ("callbacks", .ratioAtLeast .callbacks .paras 1 4),
    ("questions answered", .atMost .unanswered 0)]

/-- The structurally visible LLM-isms, none allowed. -/
def llmismFree : AStyle where
  name := "llmism-free"
  rules := [
    ("no em-dashes", .atMost .dashes 0),
    ("no colon setups", .atMost .colonSetups 0),
    ("no not-X-but-Y", .atMost .antithesis 0),
    ("no rhetorical questions", .atMost .rhetorical 0)]

def academicStyles : List AStyle := [kiran, llmismFree]

/-! ## `langlib academic <dir>` -/

open Lean

def isParaDoc (n : String) : Bool :=
  n.length == 7 && n.endsWith ".json" && (n.toList.take 2).all Char.isDigit

def loadASents (dir : String) : IO (List ASent) := do
  let names := ((← System.FilePath.readDir s!"{dir}/paragraphs").map (·.fileName)).toList.filter isParaDoc
  let mut out : List ASent := []
  for n in names.mergeSort (· ≤ ·) do
    let para := (String.ofList (n.toList.take 2)).toNat!
    match docOfString (← IO.FS.readFile s!"{dir}/paragraphs/{n}") with
    | .ok d => out := out ++ asentsOfDoc para d
    | .error e => throw (IO.userError s!"{n}: {e}")
  pure out

/-- Where each rule bites, sentence by sentence (paragraph, index in paragraph). -/
def flagged (ss : List ASent) : Json :=
  let idx := (groupParas ss).flatMap fun p => p.zipIdx.map fun (s, i) => (s, i + 1)
  let seenBefore (k : Nat) : List String := (idx.take k).flatMap fun (s, _) => names s
  let at_ (s : ASent) (i : Nat) : Json := Json.arr #[toJson s.para, toJson i]
  let newSubj := (idx.zipIdx.filter fun ((s, _), k) => k > 0 && !s.heading &&
      match s.subj with
      | some e => !given.contains e && !(seenBefore k).contains e
      | none => false).map fun ((s, i), _) => at_ s i
  let notSum := ((groupParas ss).filter fun p => multi p && !summarises p).map fun p =>
    toJson ((p.head?.map (·.para)).getD 0)
  let pick (p : ASent → Bool) := (idx.filter fun (s, _) => p s).map fun (s, i) => at_ s i
  Json.mkObj [
    ("newSubjects", Json.arr newSubj.toArray),
    ("firstNotSummary", Json.arr notSum.toArray),
    ("dashes", Json.arr (pick (·.dashes > 0)).toArray),
    ("colonSetups", Json.arr (pick (·.colonSetups > 0)).toArray),
    ("antithesis", Json.arr (pick (·.antithesis > 0)).toArray),
    ("questions", Json.arr (pick (·.asks)).toArray)]

def AFeatures.toJson (f : AFeatures) : Json :=
  Json.mkObj (AFeat.all.map fun x => (x.name, Lean.toJson (f.get x)))

def academicReport (ss : List ASent) : Json :=
  let f := AFeatures.ofSents ss
  Json.mkObj [
    ("features", f.toJson),
    ("flagged", flagged ss),
    ("styles", Json.arr (academicStyles.map fun st =>
      Json.mkObj [("name", st.name), ("holds", st.holds f),
        ("failing", Json.arr ((st.failing f).map Json.str).toArray),
        ("rules", Json.arr (st.rules.map fun (n, r) =>
          Json.mkObj [("name", n), ("rule", r.show), ("holds", r.holds f)]).toArray)]).toArray)]

def leanDef (name : String) (ss : List ASent) : String :=
  let body := ",\n   ".intercalate (ss.map fun s => Std.Format.pretty (repr s) 1000)
  s!"def {name} : List ASent :=\n  [{body}]\n"

def academicMain (dir : String) (opts : List String) : IO String := do
  let ss ← loadASents dir
  match opts with
  | ["--lean", name] => pure (leanDef name ss)
  | _ => pure (academicReport ss).pretty

/-! ## A check on the rules themselves -/

namespace Toy
/-- "Proof repair is hard. It needs invariants. Invariants are found by Sisyphus."
then "Is that enough? Sisyphus repairs ten programs." -/
def ss : List ASent :=
  [ { para := 1, words := 4, subj := some "repair", ents := [("repair", 0)] },
    { para := 1, words := 3, subj := some "repair", ents := [("repair", 0), ("inv", 2)] },
    { para := 1, words := 5, subj := some "inv", subjAt := 0, ents := [("inv", 0), ("sis", 4)] },
    { para := 2, words := 3, question := true, asks := true, ents := [("sis", 2)] },
    { para := 2, words := 4, subj := some "sis", ents := [("sis", 0), ("progs", 2)] } ]

theorem toy_kiran : kiran.failing (AFeatures.ofSents ss) = ["callbacks"] := by decide +kernel
theorem toy_llm : llmismFree.holds (AFeatures.ofSents ss) = true := by decide +kernel
end Toy

end LangLib.Style.Academic
