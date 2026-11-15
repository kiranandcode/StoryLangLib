import Lean.Data.Json
import LangLib.Json
import LangLib.Style.Core

/-!
# Academic style: information flow over checked trees

Kiran's principles for papers (`~/Documents/code/prompts/writing-style.md`) and
the structurally visible LLM-isms (`llmisms.md`) as decidable rules. As in
`Core.lean`, `asentOf` reads each sentence tree once into a flat record
(`ASent`, run by the CLI) and every feature is structural recursion over
`List ASent`, so `langlib academic <dir> --lean <name>` prints records (and the
paper's declared lore) that a theorem file restates and judges by
`decide +kernel`.

Nothing is read off raw strings. What the trees do not carry is declared:

* **in the annotation**: an entity may be `generic` (a kind) or built `of`
  earlier entities or a paragraph (`"para:5"`); every `VERB`/`AUX` leaf has a
  `VerbForm` and every finite one a `Tense`; what follows a colon or dash is
  its next sibling, with a role saying whether it elaborates something on the
  left (`appos`, an argument or list role) or is a clause (`parataxis`,
  `ccomp`, `advcl`);
* **in `lexicon.json`** beside the story: a register for every content word
  (`formal`, `informal`, `technical`, `neutral`, keyed by lemma or lower-cased
  form) and a discourse relation for the closed-class forms that signal one
  (`contrast`, `concession`, `cause`, `callback`, `neg`, `focus`, `question`,
  `quote`);
* **in `discourse.json`**: an is-a / part-of lore over entities (`isa`, pairs
  of detail and more general entity) and the paragraphs that start sections;
* **in the argument reading** (`NN.argument.json`): which entities a paragraph
  promises.

The rules, over the excerpt in reading order:

* **old to new**: a sentence's subject is given (the authors, the reader, an
  entity already mentioned, or a composite whose parts are given) and the
  entities it introduces come after the subject;
* **first sentence summarises**: the first sentence of a paragraph mentions
  an entity that covers (is, or subsumes through the lore) at least as many of
  the paragraph's sentences as its most-mentioned entity;
* **just in time**: an introduced entity is used again within three sentences,
  or was promised; the gaps are also bucketed;
* **motifs**: an entity that leaves and comes back (at least six sentences
  and a paragraph later) where both the departure and the return are at
  structurally marked points (a section's first sentence, the first or last
  sentence of a paragraph of three or more, a sentence with a contrast or
  callback connective, inside quotation marks); plain recurrence is only a
  callback;
* **question then answer**: a sentence ending in "?" or with a `question`
  word is answered by the next sentence or the first of the next paragraph;
* **colons and dashes**: *defining* when what follows elaborates the left,
  *dramatic* when a clause with its own subject follows a complete clause; the LLM-ism rule counts
  only the dramatic ones;
* **antithesis**: a negation followed by a contrast connective is a
  candidate; whether it is an antithesis (denying what nobody put forward) is
  decided in the argument world (`Argument.deny`), and a paper's theorem file
  supplies that count;
* **rhythm**: per-paragraph sentence-length jumps, short-after-long punches,
  runs of long sentences, and the overall variance;
* **register**: counts of content words per declared register.
-/

namespace LangLib.Style.Academic
open LangLib

/-! ## The declared lexicon -/

structure Lex where
  /-- register per content word, by lemma or lower-cased form -/
  reg : List (String × String) := []
  /-- discourse relation per lower-cased closed-class form -/
  rel : List (String × String) := []
  /-- multiword expressions (lower-cased forms), with a register and a relation
  ("" for none) that override their words' ("sweet spot", "at least") -/
  mwe : List (List String × String × String) := []

private def lower (s : String) : String := s.toLower
private def isWord (w : Word) : Bool := w.upos != .PUNCT && w.upos != .SYM
private def isContent (w : Word) : Bool :=
  w.upos == .NOUN || w.upos == .VERB || w.upos == .ADJ || w.upos == .ADV

/-- A register by `lemma/UPOS` first (one sense per part of speech), then by lemma. -/
def Lex.regOf (lx : Lex) (w : Word) : Option String :=
  let k := lower (w.lemma.getD w.form)
  lx.reg.lookup s!"{k}/{w.upos.name}" <|> lx.reg.lookup k
def Lex.relOf (lx : Lex) (w : Word) : Option String := lx.rel.lookup (lower w.form)
def Lex.is (lx : Lex) (w : Word) (r : String) : Bool := lx.relOf w == some r

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
  /-- entities mentioned inside quotation marks -/
  quoted : List String := []
  /-- carries a contrast, concession or callback connective -/
  frame : Bool := false
  /-- ends in "?" -/
  question : Bool := false
  /-- asks or sets up a question ("?", or a `question` word) -/
  asks : Bool := false
  colonsDef : Nat := 0
  colonsDram : Nat := 0
  dashesDef : Nat := 0
  dashesDram : Nat := 0
  /-- colons or dashes whose following constituent has no telling role -/
  unclassified : Nat := 0
  /-- a negation followed by a contrast or concession connective -/
  negTurns : Nat := 0
  formal : Nat := 0
  informal : Nat := 0
  technical : Nat := 0
  neutral : Nat := 0
  /-- content words without a register in the lexicon -/
  untagged : Nat := 0
  /-- verbs without a `VerbForm`, or finite without a `Tense` -/
  untensed : Nat := 0
  /-- carries a hedge or stance marker ("At least", "hope", "seems") -/
  hedged : Bool := false
  /-- carries a cause connective ("because", "therefore", "thus") -/
  causal : Bool := false
  /-- carries a callback connective ("again", "above", "as explained") -/
  recalls : Bool := false
  /-- entities mentioned with a demonstrative determiner ("this problem") -/
  demonstrated : List String := []
  /-- something substantial (three words or more) comes before the subject -/
  fronted : Bool := false
  /-- carries a negation -/
  negated : Bool := false
  deriving Repr, DecidableEq, Inhabited

private def roleIs (t : Tree) (r : Role) : Bool := match t with
  | .leaf w => w.role == some r
  | .node i _ => i.role == some r

private def roleOf : Tree → Option Role
  | .leaf w => w.role
  | .node i _ => i.role

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

/-- Entities mentioned inside quotation marks: a mention whose first and last
leaves are quote marks, or whose neighbouring siblings are. -/
private partial def quotedIn (lx : Lex) : Tree → List String
  | .leaf _ => []
  | .node _ kids =>
    let arr := kids.toArray
    let isQ (t : Tree) := match t with | .leaf w => lx.is w "quote" | _ => false
    let here := (List.range arr.size).filterMap fun i =>
      let k := arr[i]!
      match refOf k with
      | none => none
      | some e =>
        let ls := leavesOf k
        let inside := ls.length ≥ 3 && (ls.head?.map (lx.is · "quote")).getD false &&
          (ls.getLast?.map (lx.is · "quote")).getD false
        let around := i > 0 && isQ arr[i - 1]! && (arr[i + 1]?.map isQ).getD false
        if inside || around then some e else none
    here ++ kids.flatMap (quotedIn lx)

/-- A clause has its own subject: `nsubj`, `csubj` or expletive, down the chain of heads. -/
private partial def hasSubj : Tree → Bool
  | .leaf _ => false
  | .node _ kids => kids.any (fun k => roleIs k .nsubj || roleIs k .csubj || roleIs k .expl) ||
    kids.any fun k => match k with
      | .node i _ => i.role == some .head && hasSubj k
      | _ => false

private def isColon (w : Word) : Bool := w.form == ":"
private def isDash (w : Word) : Bool := w.form == "—" || w.form == "--"

/-- Roles of what elaborates the left: an appositive, an argument, a list. -/
def definingRoles : List Role :=
  [.appos, .obj, .iobj, .nmod, .conj, .dep, .acl, .obl, .compound, .flat, .nsubj, .xcomp,
   .amod, .nummod, .fixed, .relcl]
/-- Roles of a clause. -/
def clauseRoles : List Role := [.parataxis, .ccomp, .advcl, .csubj]
/-- Roles to look past: a connective or particle before the constituent itself. -/
def skipRoles : List Role := [.advmod, .discourse, .mark, .cc, .punct]

/-- (colon defining, colon dramatic, dash defining, dash dramatic, unclassified). -/
abbrev PCount := Nat × Nat × Nat × Nat × Nat

private def padd (a b : PCount) : PCount :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 + b.2.2.2.2)

/-- Classify every colon and dash by the constituent after it (its next
sibling, past connectives) and by whether a complete clause precedes it. -/
private partial def punctClasses : Tree → PCount
  | .leaf _ => (0, 0, 0, 0, 0)
  | .node _ kids =>
    let arr := kids.toArray
    let isLeafP (p : Word → Bool) (t : Tree) := match t with | .leaf w => p w | _ => false
    let (here, _) := (List.range arr.size).foldl (fun ((acc : PCount), (openDash : Bool)) i =>
      let k := arr[i]!
      let colon := isLeafP isColon k &&
        !(i > 0 && isLeafP isColon arr[i - 1]!) && !((arr[i + 1]?.map (isLeafP isColon)).getD false)
      let dash := isLeafP isDash k
      if dash && openDash then (acc, false) else
      if !colon && !dash then (acc, openDash) else
      let left := (List.range i).map (arr[·]!)
      let complete := left.any (fun t => roleIs t .nsubj || roleIs t .csubj || roleIs t .expl) &&
        left.any fun t => roleIs t .head || roleIs t .cop || roleIs t .root
      let next := ((List.range arr.size).filter (· > i)).map (arr[·]!) |>.find? fun t =>
        !((roleOf t).map skipRoles.contains).getD false
      let cls : Nat := match next with
        | none => 0   -- introduces a display (code, a figure): defining
        | some t =>
          -- a reveal is a clause with its own subject ("...: it is not uncommon"),
          -- not a participial adjunct ("...—granting push access")
          let clause := ((roleOf t).map clauseRoles.contains).getD false ||
            (roleOf t == none && match t with | .node j _ => j.cat == .S | _ => false)
          let leftIds := left.flatMap fun x => (mentions x 0).1.map (·.1)
          -- a clause in apposition spells out a term on the left ("The question
          -- remains: How can we ...?"): defining, if its ref names that term
          let apposClause := roleOf t == some .appos &&
            (hasSubj t || match t with | .node j _ => j.cat == .S || j.cat == .SBAR | _ => false)
          if apposClause then (if ((refOf t).map leftIds.contains).getD false then 0 else 2)
          else if clause then (if complete && hasSubj t then 1 else 0)
          else if ((roleOf t).map definingRoles.contains).getD false then 0
          else match t with
            | .node j _ => if j.cat == .NP || j.cat == .PP then 0 else 2
            | _ => 2
      let add : PCount :=
        if cls == 2 then (0, 0, 0, 0, 1)
        else if colon then (if cls == 1 then (0, 1, 0, 0, 0) else (1, 0, 0, 0, 0))
        else (if cls == 1 then (0, 0, 0, 1, 0) else (0, 0, 1, 0, 0))
      (padd acc add, dash || openDash)) (((0, 0, 0, 0, 0) : PCount), false)
    kids.foldl (fun a k => padd a (punctClasses k)) here

/-- A negation (not "not only") followed by a contrast or concession connective. -/
private partial def negTurnsIn (lx : Lex) : List Word → Nat
  | [] => 0
  | w :: rest =>
    let neg := lx.is w "neg" && !((rest.head?.map (lx.is · "focus")).getD false)
    let turn := rest.any fun v => lx.is v "contrast" || lx.is v "concession"
    if neg && turn then 1 + negTurnsIn lx (rest.dropWhile fun v => !(lx.is v "contrast" || lx.is v "concession"))
    else negTurnsIn lx rest

/-- Question words that set up a question: not inside a prepositional phrase
("the program in question"). -/
private partial def questionWords (lx : Lex) : Tree → Nat
  | .leaf w => if lx.is w "question" then 1 else 0
  | .node i kids => if i.cat == .PP then 0 else kids.foldl (fun n k => n + questionWords lx k) 0

private def feat (w : Word) (k : String) : Option String := (w.feats.find? (·.1 == k)).map (·.2)

/-- Per leaf, the register and relation after multiword expressions override. -/
def overlay (lx : Lex) (ws : List Word) : List (Option String × Option String) :=
  let forms := (ws.map (lower ·.form)).toArray
  let base := (ws.map fun w => (lx.regOf w, lx.relOf w)).toArray
  let hit (i : Nat) : Option (Nat × String × String) := lx.mwe.findSome? fun (ks, rg, rl) =>
    if ks.length ≥ 2 && (ks.zipIdx.all fun (k, j) => forms[i + j]? == some k) then some (ks.length, rg, rl) else none
  ((List.range forms.size).foldl (fun (out, skip) i =>
    if skip > 0 then (out, skip - 1) else
    match hit i with
    | some (n, rg, rl) =>
      -- an expression with no register of its own keeps its words' registers
      (out ++ ((List.range n).map fun j =>
        ((if rg == "" then (base[i + j]?.bind (·.1)) else some rg), (if rl == "" then none else some rl))), n - 1)
    | none => (out ++ [base[i]!], 0)) (([] : List (Option String × Option String)), 0)).1

/-- Entities mentioned by a phrase with a demonstrative determiner. -/
private partial def demonstratedIn (lx : Lex) : Tree → List String
  | .leaf _ => []
  | .node i kids =>
    let here := match i.ref with
      | some e => if kids.any (fun k => match k with
          | .leaf w => w.role == some .det && lx.is w "demonstrative" | _ => false) then [e] else []
      | none => []
    here ++ kids.flatMap (demonstratedIn lx)

def asentOf (lx : Lex) (para : Nat) (t : Tree) : ASent :=
  let ls := leavesOf t
  let heading : Bool := match t with | .node i _ => i.cat == .FRAG | .leaf _ => true
  let (ms, _) := mentions t 0
  let subj := mainSubj t 0
  let question := (ls.filter (·.upos == .PUNCT)).getLast?.map (·.form == "?") |>.getD false
  let (cd, cdr, dd, ddr, un) := punctClasses t
  -- in a run-in heading ("Challenge #1: ...") a colon labels what follows
  let (cd, un) := if heading then (cd + un, 0) else (cd, un)
  let ov := overlay lx ls
  let content := (ls.zip ov).filter (isContent ·.1)
  let regCount (r : String) := (content.filter (·.2.1 == some r)).length
  let hasRel (r : String) := ov.any (·.2 == some r)
  let verbs := ls.filter fun w => w.upos == .VERB || w.upos == .AUX
  { para, words := (ls.filter isWord).length, heading,
    subj := subj.bind (·.1), subjAt := (subj.map (·.2)).getD 0,
    ents := firstEach ms, quoted := quotedIn lx t,
    frame := hasRel "contrast" || hasRel "concession" || hasRel "callback",
    question, asks := question || questionWords lx t > 0,
    colonsDef := cd, colonsDram := cdr, dashesDef := dd, dashesDram := ddr, unclassified := un,
    negTurns := negTurnsIn lx ls,
    formal := regCount "formal", informal := regCount "informal",
    technical := regCount "technical", neutral := regCount "neutral",
    untagged := (content.filter (·.2.1.isNone)).length,
    hedged := hasRel "hedge", causal := hasRel "cause", recalls := hasRel "callback",
    demonstrated := demonstratedIn lx t,
    fronted := subj.isSome && (subj.map (·.2)).getD 0 ≥ 3, negated := hasRel "neg",
    untensed := (verbs.filter fun w => match feat w "VerbForm" with
      | none => true
      | some "Fin" => (feat w "Tense").isNone
      | _ => false).length }

def asentsOfDoc (lx : Lex) (para : Nat) (d : Doc) : List ASent :=
  d.sentences.map fun s => asentOf lx para s.tree

/-! ## Declared lore over entities -/

structure ALore where
  /-- (detail, more general): is-a and part-of, and each part of a composite to the composite -/
  parts : List (String × String) := []
  /-- composites: the entities they are built from, and the latest paragraph they sum up (0: none) -/
  comps : List (String × List String × Nat) := []
  /-- paragraphs that start a section -/
  sectionStarts : List Nat := []
  /-- (entity, paragraph) promised in the argument reading -/
  promised : List (String × Nat) := []
  /-- the argument reading's moves: (paragraph, sentence in it or 0, kind, term,
  terms it uses including premises) -/
  moves : List (Nat × Nat × String × String × List String) := []
  deriving Repr, DecidableEq, Inhabited

/-! ## Features (structural, kernel-friendly) -/

/-- The authors and the reader are given by the situation. -/
def given : List String := ["authors", "reader"]

def names (s : ASent) : List String := s.ents.map (·.1)

/-- Given at paragraph `para` after `seen`: a participant, mentioned, or a
composite whose parts are. -/
def isGiven (lo : ALore) (seen : List String) (para : Nat) (e : String) : Bool :=
  given.contains e || seen.contains e ||
  (lo.comps.any fun (c, ps, n) => c == e && ps.all seen.contains && n < para)

/-- `e` is `g`, or is a detail of it through the lore. -/
def under (lo : ALore) : Nat → String → String → Bool
  | 0, e, g => e == g
  | n + 1, e, g => e == g || lo.parts.any fun (d, m) => d == e && under lo n m g

def under' (lo : ALore) (e g : String) : Bool := under lo lo.parts.length e g

structure Flow where
  tracked : Nat := 0
  oldSubj : Nat := 0
  newEnts : Nat := 0
  newLate : Nat := 0
  /-- subjects given by bridging: a part or kind of something mentioned ("the tail" after "a sequence") -/
  bridged : Nat := 0
  /-- subjects that announce what the same sentence then lists ("Such changes may involve: (1) ...") -/
  announced : Nat := 0
  deriving Repr, DecidableEq

/-- `e` is a detail (part, instance) of something already mentioned. -/
def bridgedBy (lo : ALore) (seen : List String) (e : String) : Bool :=
  seen.any fun g => g != e && under' lo e g

/-- `e` is a composite whose parts the sentence names after its subject. -/
def announcedIn (lo : ALore) (s : ASent) (e : String) : Bool :=
  lo.comps.any fun (c, ps, _) => c == e && !ps.isEmpty &&
    ps.all fun x => s.ents.any fun (y, i) => y == x && i > s.subjAt

def flowFrom (lo : ALore) : List String → List ASent → Flow
  | _, [] => {}
  | seen, s :: ss =>
    let r := flowFrom lo (seen ++ names s) ss
    if s.heading || seen.isEmpty then r else
    match s.subj with
    | none => r
    | some e =>
      let news := s.ents.filter fun (x, _) => !isGiven lo seen s.para x && !bridgedBy lo seen x
      let old := isGiven lo seen s.para e
      let br := !old && bridgedBy lo seen e
      let an := !old && !br && announcedIn lo s e
      { tracked := r.tracked + 1,
        oldSubj := r.oldSubj + (if old || br || an then 1 else 0),
        newEnts := r.newEnts + news.length,
        newLate := r.newLate + (news.filter (·.2 > s.subjAt)).length,
        bridged := r.bridged + (if br then 1 else 0),
        announced := r.announced + (if an then 1 else 0) }

def groupParas : List ASent → List (List ASent)
  | [] => []
  | s :: ss => match groupParas ss with
    | (t :: ts) :: rest => if t.para == s.para then (s :: t :: ts) :: rest else [s] :: (t :: ts) :: rest
    | rest => [s] :: rest

def countMentions (e : String) : List ASent → Nat
  | [] => 0
  | s :: ss => (if (names s).contains e then 1 else 0) + countMentions e ss

/-- Sentences mentioning something `f` covers. -/
def cover (lo : ALore) (f : String) : List ASent → Nat
  | [] => 0
  | s :: ss => (if (names s).any (under' lo · f) then 1 else 0) + cover lo f ss

def distinct : List String → List String
  | [] => []
  | x :: xs => let r := distinct xs; if r.contains x then r else x :: r

/-- The paragraph's argument is about its first move's point: at least half
of its other moves are about that term or use it (a summary that paraphrases
instead of naming the details' common entity). -/
def argSummarises (lo : ALore) (para : Nat) : Bool :=
  let ms := lo.moves.filter fun (p, _, k, _, _) => p == para && k != "heading"
  -- the point is the move read at the first sentence, else the first move
  let point := (ms.find? fun (_, i, _, _, _) => i == 1) <|> ms.head?
  match point with
  | none => false
  | some m =>
    let t := m.2.2.2.1
    let rest := ms.filter (· != m)
    !rest.isEmpty && 2 * (rest.filter fun (_, _, _, t', us) => t' == t || us.contains t).length ≥ rest.length

/-- The first sentence names an entity covering at least as many sentences as
the paragraph's most-mentioned entity. -/
def summarises (lo : ALore) (ps : List ASent) : Bool :=
  let body := ps.filter (!·.heading)
  match body with
  | [] => true
  | first :: _ =>
    let es := (distinct (body.flatMap names)).filter (!given.contains ·)
    let top := es.foldl (fun m e => max m (countMentions e body)) 0
    ((names first).any fun f => !given.contains f && cover lo f body ≥ top) ||
    argSummarises lo first.para


def multi (ps : List ASent) : Bool := (ps.filter (!·.heading)).length ≥ 2

/-- Sentence indices (and paragraphs) mentioning `e`. -/
def positions (e : String) (ss : List ASent) : List (Nat × Nat) :=
  (ss.zipIdx.filter fun (s, _) => (names s).contains e).map fun (s, i) => (i, s.para)

def gapsOf : List (Nat × Nat) → List ((Nat × Nat) × (Nat × Nat))
  | a :: b :: rest => (a, b) :: gapsOf (b :: rest)
  | _ => []

def isCallback (p : (Nat × Nat) × (Nat × Nat)) : Bool := p.2.1 ≥ p.1.1 + 6 && p.2.2 != p.1.2

/-- Marked sentences of a paragraph: a section's first sentence; in a
paragraph of at least three body sentences (where first and last are
distinct from the middle), its first body sentence and its last; and every
sentence with a contrast, concession or callback connective. -/
def paraMarks (lo : ALore) (ps : List ASent) : List Bool :=
  let first := (ps.findIdx? (!·.heading)).getD 0
  let long := (ps.filter (!·.heading)).length ≥ 3
  ps.zipIdx.map fun (s, i) =>
    (i == first && lo.sectionStarts.contains s.para) ||
    (long && (i == first || i + 1 == ps.length)) || s.frame

/-- `e` is at a marked point in sentence `i`: a marked sentence, or inside quotation marks. -/
def markedAt (e : String) (marks : List Bool) (ss : List ASent) (i : Nat) : Bool :=
  marks.getD i false || ((ss[i]?.map (·.quoted.contains e)).getD false)

/-- A motif: `e` leaves and returns after a gap, and both the departure and the
return are at marked points. -/
def isMotif (e : String) (marks : List Bool) (ss : List ASent) : Bool :=
  (gapsOf (positions e ss)).any fun p =>
    isCallback p && markedAt e marks ss p.1.1 && markedAt e marks ss p.2.1

/-- A question is answered by `t`: not itself a question, sharing an entity. -/
def answers (s t : ASent) : Bool :=
  !t.question && (names s).any fun e => !given.contains e && (names t).contains e

def nextParaFirst (p : Nat) : List ASent → Option ASent
  | [] => none
  | t :: ts => if t.para != p then some t else nextParaFirst p ts

def answeredBy (s : ASent) (rest : List ASent) : Bool :=
  (match rest with | t :: _ => answers s t | [] => false) ||
  (match nextParaFirst s.para rest with | some t => answers s t | none => false)

def answeredAt : List ASent → List Bool
  | [] => []
  | s :: rest => (if s.asks then [answeredBy s rest] else []) ++ answeredAt rest

def rhetoricalIn : List ASent → Nat
  | [] => 0
  | s :: rest => (if s.question && !answeredBy s rest then 1 else 0) + rhetoricalIn rest

def sumBy (f : ASent → Nat) : List ASent → Nat
  | [] => 0
  | s :: ss => f s + sumBy f ss

/-! ### Rhythm -/

def isLong (n : Nat) : Bool := n ≥ 25
def isShort (n : Nat) : Bool := n ≤ 12

/-- Sum of absolute length changes between neighbours, and the number of neighbours. -/
def jumps : List Nat → Nat × Nat
  | a :: b :: rest => let (j, p) := jumps (b :: rest); (j + (if a ≥ b then a - b else b - a), p + 1)
  | _ => (0, 0)

/-- A short sentence right after a long one. -/
def punches : List Nat → Nat
  | a :: b :: rest => (if isLong a && isShort b then 1 else 0) + punches (b :: rest)
  | _ => 0

/-- Runs of at least three long sentences: (how many, the longest run). `cur` is the current run. -/
def runs : Nat → List Nat → Nat × Nat
  | cur, [] => (if cur ≥ 3 then 1 else 0, cur)
  | cur, x :: xs =>
    if isLong x then runs (cur + 1) xs
    else let (n, m) := runs 0 xs; ((if cur ≥ 3 then 1 else 0) + n, max cur m)

def bodyLens (ps : List ASent) : List Nat := (ps.filter (!·.heading)).map (·.words)

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
  /-- of those, used again within three sentences, or promised -/
  jit : Nat
  /-- introductions that were promised -/
  promisedIntro : Nat
  /-- first-reuse gaps: 1, 2 to 3, 4 to 6, more than 6 sentences -/
  gap1 : Nat
  gap3 : Nat
  gap6 : Nat
  gapFar : Nat
  /-- entities mentioned once -/
  single : Nat
  /-- entities recurring after a gap, anywhere -/
  callbacks : Nat
  /-- entities recurring after a gap at marked points -/
  motifs : Nat
  asks : Nat
  answered : Nat
  questions : Nat
  rhetorical : Nat
  colonsDef : Nat
  colonsDram : Nat
  dashesDef : Nat
  dashesDram : Nat
  unclassified : Nat
  negTurns : Nat
  /-- antitheses: supplied by the argument world (0 from the trees alone) -/
  antithesis : Nat
  bodySents : Nat
  lenSum : Nat
  lenSq : Nat
  jumpSum : Nat
  jumpPairs : Nat
  punches : Nat
  longRuns : Nat
  longestRun : Nat
  formal : Nat
  informal : Nat
  technical : Nat
  neutral : Nat
  untagged : Nat
  untensed : Nat
  bridged : Nat
  announced : Nat
  /-- callbacks whose return is signalled: a demonstrative, quotation marks, a callback connective -/
  deliberate : Nat
  /-- introduced entities the argument uses in the paragraph of introduction or the next -/
  neededIntro : Nat
  /-- entities the argument never uses -/
  unusedIntro : Nat
  hedgedSents : Nat
  /-- hedged sentences without a `hedge` reading, and `hedge` readings on unhedged sentences -/
  unreadHedges : Nat
  ungroundedHedges : Nat
  /-- not-X-but-Y candidates without a `deny` reading, and `deny` readings on sentences without a negation -/
  unreadDenials : Nat
  ungroundedDenials : Nat
  /-- sentences with a cause connective without an `infer` reading, and `infer` readings without one -/
  unreadReasons : Nat
  ungroundedReasons : Nat
  frontings : Nat
  /-- paragraphs of two or more sentences ending on a short one -/
  shortClosers : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Sentence `i` (1-based) of paragraph `p`. -/
def sentAt (ss : List ASent) (idxs : List (Nat × Nat)) (p i : Nat) : Option ASent :=
  ((ss.zip idxs).find? fun (_, (q, j)) => q == p && j == i).map (·.1)

/-- The argument reads sentence `(p, i)` with a move of one of `kinds`. -/
def readAs (lo : ALore) (kinds : List String) (p i : Nat) : Bool :=
  lo.moves.any fun (q, j, k, _, _) => q == p && j == i && kinds.contains k

/-- Readings of kind `k` whose sentence lacks the mark `has`. -/
def ungrounded (lo : ALore) (ss : List ASent) (idxs : List (Nat × Nat)) (k : String) (has : ASent → Bool) : Nat :=
  (lo.moves.filter fun (p, i, k', _, _) => k' == k &&
    !((sentAt ss idxs p i).map has).getD false).length

def AFeatures.ofSents (lo : ALore) (ss : List ASent) : AFeatures :=
  let fl := flowFrom lo [] ss
  let ps := groupParas ss
  let marks := ps.flatMap (paraMarks lo)
  let es := (distinct (ss.flatMap names)).filter (!given.contains ·)
  let poss := es.map fun e => (e, positions e ss)
  let reused := poss.filter (·.2.length ≥ 2)
  let firstGap (p : List (Nat × Nat)) : Nat := match p with
    | a :: b :: _ => b.1 - a.1 | _ => 0
  let promisedAt (e : String) (p : List (Nat × Nat)) : Bool := match p with
    | a :: _ => lo.promised.any fun (x, n) => x == e && n ≤ a.2
    | [] => false
  let ans := answeredAt ss
  let idxs := ps.flatMap fun p => p.zipIdx.map fun (s, i) => (s.para, i + 1)
  let tagged := ss.zip idxs
  let unread (has : ASent → Bool) (kinds : List String) : Nat :=
    (tagged.filter fun (s, (p, i)) => has s && !readAs lo kinds p i).length
  let deliberateAt (e : String) (i : Nat) : Bool := match ss[i]? with
    | some s => s.demonstrated.contains e || s.quoted.contains e || s.recalls
    | none => false
  let usedIn (e : String) (p : Nat) : Bool := lo.moves.any fun (q, _, _, t, us) =>
    (q == p || q == p + 1) && (t == e || us.contains e)
  let usedAnywhere (e : String) : Bool := lo.moves.any fun (_, _, _, t, us) => t == e || us.contains e
  let lens := ps.map bodyLens
  let bl := lens.flatMap id
  let js := lens.map jumps
  let rs := lens.map (runs 0)
  { sents := ss.length, words := sumBy (·.words) ss, paras := ps.length,
    multiParas := (ps.filter multi).length,
    firstSum := (ps.filter fun p => multi p && summarises lo p).length,
    tracked := fl.tracked, oldSubj := fl.oldSubj, newEnts := fl.newEnts, newLate := fl.newLate,
    reused := reused.length,
    jit := (reused.filter fun (e, p) => firstGap p ≤ 3 || promisedAt e p).length,
    promisedIntro := (poss.filter fun (e, p) => promisedAt e p).length,
    gap1 := (reused.filter fun (_, p) => firstGap p ≤ 1).length,
    gap3 := (reused.filter fun (_, p) => firstGap p ≥ 2 && firstGap p ≤ 3).length,
    gap6 := (reused.filter fun (_, p) => firstGap p ≥ 4 && firstGap p ≤ 6).length,
    gapFar := (reused.filter fun (_, p) => firstGap p > 6).length,
    single := (poss.filter (·.2.length ≤ 1)).length,
    callbacks := (poss.filter fun (_, p) => (gapsOf p).any isCallback).length,
    motifs := (es.filter fun e => isMotif e marks ss).length,
    asks := ans.length, answered := (ans.filter id).length,
    questions := (ss.filter (·.question)).length, rhetorical := rhetoricalIn ss,
    colonsDef := sumBy (·.colonsDef) ss, colonsDram := sumBy (·.colonsDram) ss,
    dashesDef := sumBy (·.dashesDef) ss, dashesDram := sumBy (·.dashesDram) ss,
    unclassified := sumBy (·.unclassified) ss, negTurns := sumBy (·.negTurns) ss,
    antithesis := 0,
    bodySents := bl.length, lenSum := bl.foldl (· + ·) 0, lenSq := bl.foldl (fun a x => a + x * x) 0,
    jumpSum := (js.map (·.1)).foldl (· + ·) 0, jumpPairs := (js.map (·.2)).foldl (· + ·) 0,
    punches := (lens.map Academic.punches).foldl (· + ·) 0,
    longRuns := (rs.map (·.1)).foldl (· + ·) 0, longestRun := (rs.map (·.2)).foldl max 0,
    formal := sumBy (·.formal) ss, informal := sumBy (·.informal) ss,
    technical := sumBy (·.technical) ss, neutral := sumBy (·.neutral) ss,
    untagged := sumBy (·.untagged) ss, untensed := sumBy (·.untensed) ss,
    bridged := fl.bridged, announced := fl.announced,
    deliberate := (poss.filter fun (e, p) => (gapsOf p).any fun q => isCallback q && deliberateAt e q.2.1).length,
    neededIntro := (poss.filter fun (e, p) => match p with | a :: _ => usedIn e a.2 | [] => false).length,
    unusedIntro := (es.filter (!usedAnywhere ·)).length,
    hedgedSents := (ss.filter (·.hedged)).length,
    unreadHedges := unread (·.hedged) ["hedge"],
    ungroundedHedges := ungrounded lo ss idxs "hedge" (fun s => s.hedged || s.asks),
    unreadDenials := unread (·.negTurns > 0) ["deny"],
    ungroundedDenials := ungrounded lo ss idxs "deny" (·.negated),
    unreadReasons := unread (·.causal) ["infer"],
    ungroundedReasons := ungrounded lo ss idxs "infer" (·.causal),
    frontings := (ss.filter fun s => s.fronted && !s.heading).length,
    shortClosers := (lens.filter fun l => l.length ≥ 2 && ((l.getLast?.map isShort).getD false)).length }

inductive AFeat where
  | sents | words | paras | multiParas | firstSum | tracked | oldSubj | newEnts | newLate
  | reused | jit | promisedIntro | gap1 | gap3 | gap6 | gapFar | single | callbacks | motifs
  | asks | answered | unanswered | questions | rhetorical
  | colonsDef | colonsDram | dashesDef | dashesDram | dashes | unclassified | negTurns | antithesis
  | bodySents | lenSum | lenSq | jumpSum | jumpPairs | punches | longRuns | longestRun
  | formal | informal | technical | neutral | untagged | untensed | contentWords
  | bridged | announced | deliberate | neededIntro | unusedIntro | hedgedSents
  | unreadHedges | ungroundedHedges | unreadDenials | ungroundedDenials | unreadReasons | ungroundedReasons
  | frontings | shortClosers
  deriving Repr, DecidableEq, Inhabited

def AFeatures.get (f : AFeatures) : AFeat → Nat
  | .sents => f.sents | .words => f.words | .paras => f.paras | .multiParas => f.multiParas
  | .firstSum => f.firstSum | .tracked => f.tracked | .oldSubj => f.oldSubj
  | .newEnts => f.newEnts | .newLate => f.newLate | .reused => f.reused | .jit => f.jit
  | .promisedIntro => f.promisedIntro | .gap1 => f.gap1 | .gap3 => f.gap3 | .gap6 => f.gap6
  | .gapFar => f.gapFar | .single => f.single | .callbacks => f.callbacks | .motifs => f.motifs
  | .asks => f.asks | .answered => f.answered | .unanswered => f.asks - f.answered
  | .questions => f.questions | .rhetorical => f.rhetorical
  | .colonsDef => f.colonsDef | .colonsDram => f.colonsDram | .dashesDef => f.dashesDef
  | .dashesDram => f.dashesDram | .dashes => f.dashesDef + f.dashesDram
  | .unclassified => f.unclassified | .negTurns => f.negTurns | .antithesis => f.antithesis
  | .bodySents => f.bodySents | .lenSum => f.lenSum | .lenSq => f.lenSq
  | .jumpSum => f.jumpSum | .jumpPairs => f.jumpPairs | .punches => f.punches
  | .longRuns => f.longRuns | .longestRun => f.longestRun
  | .formal => f.formal | .informal => f.informal | .technical => f.technical
  | .neutral => f.neutral | .untagged => f.untagged | .untensed => f.untensed
  | .contentWords => f.formal + f.informal + f.technical + f.neutral + f.untagged
  | .bridged => f.bridged
  | .announced => f.announced
  | .deliberate => f.deliberate
  | .neededIntro => f.neededIntro
  | .unusedIntro => f.unusedIntro
  | .hedgedSents => f.hedgedSents
  | .unreadHedges => f.unreadHedges
  | .ungroundedHedges => f.ungroundedHedges
  | .unreadDenials => f.unreadDenials
  | .ungroundedDenials => f.ungroundedDenials
  | .unreadReasons => f.unreadReasons
  | .ungroundedReasons => f.ungroundedReasons
  | .frontings => f.frontings
  | .shortClosers => f.shortClosers

def AFeat.name : AFeat → String
  | .sents => "sents" | .words => "words" | .paras => "paras" | .multiParas => "multiParas"
  | .firstSum => "firstSum" | .tracked => "tracked" | .oldSubj => "oldSubj"
  | .newEnts => "newEnts" | .newLate => "newLate" | .reused => "reused" | .jit => "jit"
  | .promisedIntro => "promisedIntro" | .gap1 => "gap1" | .gap3 => "gap3" | .gap6 => "gap6"
  | .gapFar => "gapFar" | .single => "single" | .callbacks => "callbacks" | .motifs => "motifs"
  | .asks => "asks" | .answered => "answered" | .unanswered => "unanswered"
  | .questions => "questions" | .rhetorical => "rhetorical"
  | .colonsDef => "colonsDef" | .colonsDram => "colonsDram" | .dashesDef => "dashesDef"
  | .dashesDram => "dashesDram" | .dashes => "dashes" | .unclassified => "unclassified"
  | .negTurns => "negTurns" | .antithesis => "antithesis"
  | .bodySents => "bodySents" | .lenSum => "lenSum" | .lenSq => "lenSq"
  | .jumpSum => "jumpSum" | .jumpPairs => "jumpPairs" | .punches => "punches"
  | .longRuns => "longRuns" | .longestRun => "longestRun"
  | .formal => "formal" | .informal => "informal" | .technical => "technical"
  | .neutral => "neutral" | .untagged => "untagged" | .untensed => "untensed"
  | .contentWords => "contentWords"
  | .bridged => "bridged"
  | .announced => "announced"
  | .deliberate => "deliberate"
  | .neededIntro => "neededIntro"
  | .unusedIntro => "unusedIntro"
  | .hedgedSents => "hedgedSents"
  | .unreadHedges => "unreadHedges"
  | .ungroundedHedges => "ungroundedHedges"
  | .unreadDenials => "unreadDenials"
  | .ungroundedDenials => "ungroundedDenials"
  | .unreadReasons => "unreadReasons"
  | .ungroundedReasons => "ungroundedReasons"
  | .frontings => "frontings"
  | .shortClosers => "shortClosers"

def AFeat.all : List AFeat :=
  [.sents, .words, .paras, .multiParas, .firstSum, .tracked, .oldSubj, .newEnts, .newLate,
   .reused, .jit, .promisedIntro, .gap1, .gap3, .gap6, .gapFar, .single, .callbacks, .motifs,
   .asks, .answered, .unanswered, .questions, .rhetorical,
   .colonsDef, .colonsDram, .dashesDef, .dashesDram, .dashes, .unclassified, .negTurns, .antithesis,
   .bodySents, .lenSum, .lenSq, .jumpSum, .jumpPairs, .punches, .longRuns, .longestRun,
   .formal, .informal, .technical, .neutral, .untagged, .untensed, .contentWords,
   .bridged, .announced, .deliberate, .neededIntro, .unusedIntro, .hedgedSents, .unreadHedges, .ungroundedHedges, .unreadDenials, .ungroundedDenials, .unreadReasons, .ungroundedReasons, .frontings, .shortClosers]

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

/-- Kiran's principles for papers (thresholds are judgement calls). -/
def kiran : AStyle where
  name := "kiran"
  rules := [
    ("old to new: subjects given", .ratioAtLeast .oldSubj .tracked 3 4),
    ("old to new: new comes late", .ratioAtLeast .newLate .newEnts 2 3),
    ("first sentence summarises", .ratioAtLeast .firstSum .multiParas 2 3),
    ("just in time", .ratioAtLeast .jit .reused 1 2),
    ("motifs", .ratioAtLeast .motifs .paras 1 8),
    ("questions answered", .atMost .unanswered 0)]

/-- The structurally visible LLM-isms, none allowed: dramatic colons and dashes
(defining ones are allowed), antitheses, rhetorical questions. -/
def llmismFree : AStyle where
  name := "llmism-free"
  rules := [
    ("no dramatic dashes", .atMost .dashesDram 0),
    ("no dramatic colons", .atMost .colonsDram 0),
    ("no not-X-but-Y", .atMost .antithesis 0),
    ("no rhetorical questions", .atMost .rhetorical 0)]

/-- Kiran's literal rule: no em-dashes at all. -/
def noDashes : AStyle where
  name := "no-em-dashes"
  rules := [("no em-dashes", .atMost .dashes 0)]

/-- The annotation carries every mark the rules read. -/
def annotated : AStyle where
  name := "annotated"
  rules := [
    ("every verb has a form and finite ones a tense", .atMost .untensed 0),
    ("every colon and dash classified", .atMost .unclassified 0),
    ("every content word has a register", .atMost .untagged 0)]

/-- The argument reading is grounded in the text both ways: every hedge,
not-X-but-Y and stated reason the trees mark is read as a move, and every
hedge or denial read sits on a sentence that marks it. -/
def grounded : AStyle where
  name := "grounded"
  rules := [
    ("hedges read", .atMost .unreadHedges 0),
    ("hedge readings grounded", .atMost .ungroundedHedges 0),
    ("denials read", .atMost .unreadDenials 0),
    ("denial readings grounded", .atMost .ungroundedDenials 0),
    ("reasons read", .atMost .unreadReasons 0)]

def academicStyles : List AStyle := [kiran, llmismFree, noDashes, annotated, grounded]

/-! ## `langlib academic <dir>` -/

open Lean

def isParaDoc (n : String) : Bool :=
  n.length == 7 && n.endsWith ".json" && (n.toList.take 2).all Char.isDigit

private def readJson? (p : String) : IO (Option Json) := do
  if !(← System.FilePath.pathExists p) then return none
  match Json.parse (← IO.FS.readFile p) with
  | .ok j => pure (some j)
  | .error e => throw (IO.userError s!"{p}: {e}")

/-- `lexicon.json`: `{key: {"reg": r, "rel": r}}` (or `{key: r}` for a register). -/
def loadLex (dir : String) : IO Lex := do
  let some (.obj kvs) ← readJson? s!"{dir}/lexicon.json" | pure {}
  let mut reg := #[]
  let mut rel := #[]
  let mut mwe := #[]
  for (k, v) in kvs.toList do
    let rg := match v with
      | .str r => r
      | j => (j.getObjValAs? String "reg").toOption.getD ""
    let rl := (v.getObjValAs? String "rel").toOption.getD ""
    if k.contains ' ' then
      mwe := mwe.push ((k.splitOn " ").filter (· != ""), rg, rl)
    else
      if rg != "" then reg := reg.push (k, rg)
      if rl != "" then rel := rel.push (k, rl)
  -- longer expressions first, so ", so long as" wins over ", so"
  pure { reg := reg.toList, rel := rel.toList,
         mwe := mwe.toList.mergeSort fun a b => a.1.length ≥ b.1.length }

def loadAll (dir : String) : IO (List ASent × ALore × List String) := do
  let lx ← loadLex dir
  let names := ((← System.FilePath.readDir s!"{dir}/paragraphs").map (·.fileName)).toList.filter isParaDoc
  let mut out : List ASent := []
  let mut comps : List (String × List String × Nat) := []
  let mut promised : List (String × Nat) := []
  let mut moves : List (Nat × Nat × String × String × List String) := []
  let mut known : List String := []
  for n in names.mergeSort (· ≤ ·) do
    let para := (String.ofList (n.toList.take 2)).toNat!
    match docOfString (← IO.FS.readFile s!"{dir}/paragraphs/{n}") with
    | .ok d =>
      out := out ++ asentsOfDoc lx para d
      known := known ++ d.entities.map (·.id)
      for e in d.entities do
        if !e.of.isEmpty && !comps.any (·.1 == e.id) then
          let ents := e.of.filter (!·.startsWith "para:")
          let ps := e.of.filterMap fun s => if s.startsWith "para:" then (s.drop 5).toString.toNat? else none
          comps := comps ++ [(e.id, ents, ps.foldl max 0)]
    | .error e => throw (IO.userError s!"{n}: {e}")
    let arg := s!"{dir}/paragraphs/{String.ofList (n.toList.take 2)}.argument.json"
    if let some j ← readJson? arg then
      if let .ok (.arr ms) := j.getObjVal? "moves" then
        for m in ms do
          let mv := (m.getObjValAs? String "move").toOption.getD ""
          let strs (k : String) : List String := (m.getObjValAs? (List String) k).toOption.getD []
          let term := (m.getObjValAs? String "t").toOption.getD ((m.getObjValAs? String "a").toOption.getD "")
          let uses := strs "uses" ++ strs "premises" ++ ((m.getObjValAs? String "b").toOption.map ([·])).getD []
          let si := (m.getObjValAs? Nat "s").toOption.getD 0
          moves := moves ++ [(para, si, mv, term, uses)]
          if mv == "promise" || mv == "contribute" || mv == "hedge" then
            if let .ok t := m.getObjValAs? String "t" then promised := promised ++ [(t, para)]
  let mut parts : List (String × String) := comps.flatMap fun (c, ps, _) => ps.map (·, c)
  let mut starts : List Nat := []
  let mut problems : List String := []
  if let some j ← readJson? s!"{dir}/discourse.json" then
    if let .ok (.arr xs) := j.getObjVal? "isa" then
      for x in xs do
        match x with
        | .arr #[.str a, .str b] =>
          for e in [a, b] do
            if !known.contains e then problems := problems ++ [s!"isa names unknown entity {e}"]
          parts := parts ++ [(a, b)]
        | _ => problems := problems ++ ["isa entries are [detail, general] pairs"]
    if let .ok (.arr xs) := j.getObjVal? "sections" then
      starts := xs.toList.filterMap fun x => (x.getNat?).toOption
  for (c, ps, _) in comps do
    for p in ps do
      if !known.contains p then problems := problems ++ [s!"composite {c} is of unknown entity {p}"]
  pure (out, { parts, comps, sectionStarts := starts, promised, moves }, problems)

/-- Where each rule bites, sentence by sentence (paragraph, index in paragraph). -/
def flagged (lo : ALore) (ss : List ASent) : Json :=
  let idx := (groupParas ss).flatMap fun p => p.zipIdx.map fun (s, i) => (s, i + 1)
  let seenBefore (k : Nat) : List String := (idx.take k).flatMap fun (s, _) => names s
  let at_ (s : ASent) (i : Nat) : Json := Json.arr #[toJson s.para, toJson i]
  let newSubj := (idx.zipIdx.filter fun ((s, _), k) => k > 0 && !s.heading &&
      match s.subj with
      | some e => !isGiven lo (seenBefore k) s.para e
      | none => false).map fun ((s, i), _) => at_ s i
  let notSum := ((groupParas ss).filter fun p => multi p && !summarises lo p).map fun p =>
    toJson ((p.head?.map (·.para)).getD 0)
  let marks := (groupParas ss).flatMap (paraMarks lo)
  let es := (distinct (ss.flatMap names)).filter (!given.contains ·)
  let motifs := es.filter fun e => isMotif e marks ss
  let pick (p : ASent → Bool) := (idx.filter fun (s, _) => p s).map fun (s, i) => at_ s i
  Json.mkObj [
    ("newSubjects", Json.arr newSubj.toArray),
    ("firstNotSummary", Json.arr notSum.toArray),
    ("motifs", Json.arr (motifs.map Json.str).toArray),
    ("dramaticDashes", Json.arr (pick (·.dashesDram > 0)).toArray),
    ("definingDashes", Json.arr (pick (·.dashesDef > 0)).toArray),
    ("dramaticColons", Json.arr (pick (·.colonsDram > 0)).toArray),
    ("definingColons", Json.arr (pick (·.colonsDef > 0)).toArray),
    ("unclassified", Json.arr (pick (·.unclassified > 0)).toArray),
    ("negTurns", Json.arr (pick (·.negTurns > 0)).toArray),
    ("questions", Json.arr (pick (·.asks)).toArray),
    ("untensed", Json.arr (pick (·.untensed > 0)).toArray),
    ("hedged", Json.arr (pick (·.hedged)).toArray),
    ("causal", Json.arr (pick (·.causal)).toArray),
    ("negated", Json.arr (pick (·.negated)).toArray)]

def AFeatures.toJson (f : AFeatures) : Json :=
  Json.mkObj (AFeat.all.map fun x => (x.name, Lean.toJson (f.get x)))

def academicReport (ss : List ASent) (lo : ALore) (problems : List String) : Json :=
  let f := AFeatures.ofSents lo ss
  Json.mkObj [
    ("features", f.toJson),
    ("loreProblems", Json.arr (problems.map Json.str).toArray),
    ("flagged", flagged lo ss),
    ("styles", Json.arr (academicStyles.map fun st =>
      Json.mkObj [("name", st.name), ("holds", st.holds f),
        ("failing", Json.arr ((st.failing f).map Json.str).toArray),
        ("rules", Json.arr (st.rules.map fun (n, r) =>
          Json.mkObj [("name", n), ("rule", r.show), ("holds", r.holds f)]).toArray)]).toArray)]

def leanDef (name : String) (ss : List ASent) (lo : ALore) : String :=
  let body := ",\n   ".intercalate (ss.map fun s => Std.Format.pretty (repr s) 1000)
  s!"def {name} : List ASent :=\n  [{body}]\n\ndef {name}Lore : ALore :=\n  {Std.Format.pretty (repr lo) 1000000}\n"

def academicMain (dir : String) (opts : List String) : IO String := do
  let (ss, lo, problems) ← loadAll dir
  match opts with
  | ["--lean", name] => pure (leanDef name ss lo)
  | _ => pure (academicReport ss lo problems).pretty

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

theorem toy_kiran : kiran.failing (AFeatures.ofSents {} ss) = ["motifs"] := by decide +kernel
theorem toy_llm : llmismFree.holds (AFeatures.ofSents {} ss) = true := by decide +kernel

/-- "These two" is a composite of repair and inv: a given subject, not a new one. -/
def ss2 : List ASent :=
  [ { para := 1, words := 4, subj := some "repair", ents := [("repair", 0), ("inv", 3)] },
    { para := 2, words := 5, subj := some "both", ents := [("both", 0), ("sis", 4)] } ]
def lo2 : ALore := { comps := [("both", ["repair", "inv"], 0)], parts := [("repair", "both"), ("inv", "both")] }
theorem toy_composite : (AFeatures.ofSents lo2 ss2).oldSubj = 1 := by decide +kernel
theorem toy_composite_off : (AFeatures.ofSents {} ss2).oldSubj = 0 := by decide +kernel

/-- A first sentence naming the general term summarises its details through the lore. -/
def ss3 : List ASent :=
  [ { para := 1, words := 6, subj := some "authors", ents := [("authors", 0), ("align", 3)] },
    { para := 1, words := 6, subj := some "traces", ents := [("traces", 0)] },
    { para := 1, words := 6, subj := some "traces", ents := [("traces", 0), ("values", 2)] } ]
def lo3 : ALore := { parts := [("traces", "align"), ("values", "align")] }
theorem toy_summary : (AFeatures.ofSents lo3 ss3).firstSum = 1 := by decide +kernel
theorem toy_summary_off : (AFeatures.ofSents {} ss3).firstSum = 0 := by decide +kernel

/-- Rhythm: two long sentences, then a punch. -/
theorem toy_rhythm : punches [30, 28, 6] = 1 ∧ runs 0 [30, 28, 26, 4] = (1, 3) ∧ jumps [30, 28, 6] = (24, 2) := by
  decide +kernel
end Toy

end LangLib.Style.Academic
