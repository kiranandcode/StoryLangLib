import LangLib.Basic

/-!
# Style as decidable predicates over checked documents

A paragraph's langlib document is a list of typed trees whose leaves are its
tokens. A *style feature* is a function of those trees: how long the sentences
are and how deep, how many asides they carry, how often the narrator
generalises, how much of the text is speech. A *style* is a list of named
rules over the features (bounds, ratios by cross-multiplication, and structural
rules such as "every footnote has its anchor"), so whether a story is in a
style is decidable, and `decide +kernel` proves it.

Two layers, so proofs stay cheap:

* `sentOf` reads one sentence tree into a `Sent`, a flat record of counts and a
  few strings (`partial`, run by the CLI, never by the kernel);
* `Features.ofSents` and `Style.failing` are plain structural recursion over
  `List Sent`, so a story's records, printed as a Lean term by
  `langlib style <dir> --lean <name>`, can be restated and judged by `decide`.

Annotation conventions the features read:

* **Footnotes.** The anchor is a leaf `{"w": "*", "p": "SYM", "r": "dep"}`
  (or `†`, `‡`) that is a direct child of its sentence's root. The footnote is a
  sentence of its own, later in the same paragraph, whose root is a `PRN` node
  starting with a leaf of the same symbol (role `mark`).
* **Generic statements** (the narrator generalising: "People are like that"): a
  clause outside quotes whose finite verb, copula or auxiliary carries
  `"f": {"Tense": "Pres"}` and whose subject is not a character.
* **Similes**: a `PP` whose case marker is "like", not attached to a noun
  (`nmod`: "languages like C" gives examples); a clause marked "as if" or
  "as though"; "as ADJ as ...".
* **Capitalised Concepts**: a common noun (`NOUN`, not `PROPN`) spelled with a
  capital that is not first in its sentence or after `. ? ! : "` or a dash.
-/

namespace LangLib.Style
open LangLib

/-! ## Word lists -/

def footMarks : List String := ["*", "†", "‡", "§"]

/-- Verbs of speaking that tag a quote. -/
def speechTagVerbs : List String :=
  ["say", "tell", "ask", "answer", "reply", "whisper", "shout", "call", "laugh", "murmur",
   "mutter", "snap", "add", "agree", "explain", "announce", "cry", "sigh", "grin", "admit",
   "insist", "demand", "observe", "remark", "continue", "begin", "protest", "breathe"]

/-- Verbs of perception and cognition: a clause with one, whose subject is the
point-of-view character, is focalised interiority. -/
def interiorVerbs : List String :=
  ["think", "know", "feel", "want", "notice", "wonder", "realise", "realize", "hear", "see",
   "mean", "believe", "hope", "wish", "remember", "forget", "decide", "need", "suppose",
   "suspect", "doubt", "imagine", "expect", "fear", "love", "hate", "mind", "care",
   "understand", "guess", "like", "taste",
   "smell", "sense", "recognise", "recognize", "trust", "dread", "miss"]

/-- Openers that relate a sentence to the one before. -/
def connectiveRoles : List Role := [.cc, .advmod, .mark, .discourse]

def terminalPunct : List String := [".", "?", "!", "...", "…", "\"", "”", "'", "’"]

/-- Tokens after which a capital is expected. -/
def capAfter : List String := [".", "?", "!", ":", "\"", "“", "—", "--", "-", "…", "...", "("] ++ footMarks

private def lower (s : String) : String := s.toLower

private def lemmaOf (w : Word) : String := lower (w.lemma.getD w.form)

private def isWord (w : Word) : Bool := w.upos != .PUNCT && w.upos != .SYM

private def roleIs (t : Tree) (r : Role) : Bool := match t with
  | .leaf w => w.role == some r
  | .node i _ => i.role == some r

private def tense (w : Word) : Option String := (w.feats.find? (·.1 == "Tense")).map (·.2)

/-- The entity a constituent mentions. -/
private partial def refOf : Tree → Option EntityId
  | .leaf w => w.ref
  | .node i kids => i.ref <|> kids.findSome? fun k => match k with
    | .leaf w => if w.role == some .head then w.ref else none
    | .node j _ => if j.cat == .NP || j.role == some .head then refOf k else none

private partial def depth : Tree → Nat
  | .leaf _ => 1
  | .node _ kids => 1 + (kids.map depth).foldl max 0

private partial def leaves : Tree → List Word
  | .leaf w => [w]
  | .node _ kids => kids.flatMap leaves

/-! ## Per sentence -/

/-- What one sentence tree contributes to a story's style. -/
structure Sent where
  /-- the paragraph it is in (1-based) -/
  para : Nat := 0
  /-- words: leaves that are not punctuation or footnote marks -/
  words : Nat := 0
  depth : Nat := 0
  /-- parenthetical (`PRN`) nodes, not counting a footnote's own root -/
  prn : Nat := 0
  /-- footnote anchors in this sentence, by mark -/
  anchors : List String := []
  /-- the mark of the footnote this sentence is, if it is one -/
  footnote : Option String := none
  /-- an anchor sentence without its marks still has a clause and ends in terminal punctuation -/
  wholeWithout : Bool := true
  clauses : Nat := 0
  /-- generic present-tense clauses (the narrator generalising), outside quotes -/
  generics : Nat := 0
  /-- "like" + noun phrase -/
  likeSimiles : Nat := 0
  /-- "as if", "as though" -/
  asIf : Nat := 0
  /-- "as ADJ as ..." -/
  asAs : Nat := 0
  /-- capitalised common nouns not in a capital's position -/
  concepts : Nat := 0
  /-- words inside quotes -/
  quoteWords : Nat := 0
  /-- lemmas of the verbs tagging quotes -/
  tags : List String := []
  /-- the sentence's opening connective, if it opens with one -/
  opener : Option String := none
  /-- clauses of perception or cognition with the point-of-view character as subject -/
  interior : Nat := 0
  /-- clauses with a character as subject that are not interiority (choreography) -/
  choreo : Nat := 0
  /-- clauses outside quotes whose subject is the point-of-view character -/
  povClauses : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Counts one tree contributes (merged bottom-up). -/
structure Acc where
  prn : Nat := 0
  clauses : Nat := 0
  generics : Nat := 0
  likeSimiles : Nat := 0
  asIf : Nat := 0
  asAs : Nat := 0
  quoteWords : Nat := 0
  tags : List String := []
  interior : Nat := 0
  choreo : Nat := 0
  povClauses : Nat := 0
  deriving Inhabited

def Acc.add (a b : Acc) : Acc :=
  { prn := a.prn + b.prn, clauses := a.clauses + b.clauses, generics := a.generics + b.generics,
    likeSimiles := a.likeSimiles + b.likeSimiles, asIf := a.asIf + b.asIf, asAs := a.asAs + b.asAs,
    quoteWords := a.quoteWords + b.quoteWords, tags := a.tags ++ b.tags,
    interior := a.interior + b.interior, choreo := a.choreo + b.choreo,
    povClauses := a.povClauses + b.povClauses }

/-- Who the story is about: its point-of-view character and its cast. -/
structure Ctx where
  pov : String := ""
  chars : List String := []
  /-- the text is a paper (`"kind": "paper"` in story.json) -/
  paper : Bool := false
  /-- in a paper, the entities that are individuals (not `generic` kinds): a
  present-tense clause about one of them reports, it does not generalise -/
  specific : List String := []

structure Down where
  subj : Option EntityId := none
  tense : Option String := none
  quoted : Bool := false
  /-- under a verb of saying: reported speech, not the narrator's -/
  said : Bool := false

/-- The head verb of a node: a direct `VERB` head leaf, else that of its head `VP`. -/
private def headVerb (kids : List Tree) : Option Word :=
  let direct := kids.findSome? fun k => match k with
    | .leaf w => if w.upos == .VERB && w.role == some .head then some w else none
    | _ => none
  direct <|> kids.findSome? fun k => match k with
    | .node i kk => if i.cat == .VP && i.role == some .head then
        kk.findSome? fun x => match x with
          | .leaf w => if w.upos == .VERB && w.role == some .head then some w else none
          | _ => none
      else none
    | _ => none

private def firstWordForm : List Tree → Option String
  | [] => none
  | .leaf w :: rest => if w.upos == .PUNCT then firstWordForm rest else some (lower w.form)
  | .node _ _ :: _ => none

partial def accOf (cx : Ctx) (d : Down) : Tree → Acc
  | .leaf w => if d.quoted && isWord w then { quoteWords := 1 } else {}
  | .node info kids =>
    let quoted := d.quoted || info.cat == .QUOTE
    let ownSubj := (kids.find? (roleIs · .nsubj)).bind refOf
    let subj := ownSubj <|> d.subj
    let ownTense := (kids.filterMap fun k => match k with
      | .leaf w => if w.role == some .aux || w.role == some .cop ||
          (w.upos == .VERB && w.role == some .head) then tense w else none
      | _ => none).head?
    let tns := ownTense <|> d.tense
    let verb := kids.findSome? fun k => match k with
      | .leaf w => if w.upos == .VERB && w.role == some .head then some w else none
      | _ => none
    let isClause := verb.isSome || kids.any (roleIs · .cop)
    let charSubj := match subj with | some e => cx.chars.contains e | none => false
    let here : Acc :=
      if !isClause then {} else
      let lem := (verb.map lemmaOf).getD "be"
      let reflexive := kids.any fun k => match k with
        | .leaf w => w.role == some .obj && ["herself", "himself", "themselves", "myself"].contains (lower w.form)
        | _ => false
      -- a verb of mind, a state she is in ("she was annoyed"), or telling herself
      let interior := !quoted && subj == some cx.pov &&
        (interiorVerbs.contains lem || lem == "be" || (lem == "tell" && reflexive))
      { clauses := 1,
        generics := if !quoted && !d.said && tns == some "Pres" && !charSubj &&
          !(match subj with | some e => cx.specific.contains e | none => false) then 1 else 0,
        interior := if interior then 1 else 0,
        choreo := if !quoted && charSubj && !interior then 1 else 0,
        povClauses := if !quoted && subj == some cx.pov then 1 else 0 }
    let prn : Acc := if info.cat == .PRN && !quoted then { prn := 1 } else {}
    -- a "like" phrase attached to a noun ("languages like C and C++") gives
    -- examples; only one attached to a verb or clause compares
    -- in a paper, "like" with a tracked entity ("like C++, Rust supports ...")
    -- compares two things the text is about: a literal comparison, not an image
    let literal := cx.paper && kids.any fun k => match k with
      | .node j _ => j.ref.isSome
      | .leaf w => w.ref.isSome && w.role == some .head
    let like : Acc := if info.cat == .PP && info.role != some .nmod && !literal && kids.any (fun k => match k with
        | .leaf w => w.role == some .case && lower w.form == "like" | _ => false) then { likeSimiles := 1 } else {}
    let marks := " ".intercalate (kids.filterMap fun k => match k with
      | .leaf w => if w.role == some .mark || w.role == some .fixed then some (lower w.form) else none
      | _ => none)
    let asif : Acc := if marks == "as if" || marks == "as though" then { asIf := 1 } else {}
    -- "as ADJ as ...": an "as" adverb with a later PP or clause opening with "as"
    let asas : Acc :=
      let idx := kids.findIdx? fun k => match k with
        | .leaf w => w.upos == .ADV && lower w.form == "as" | _ => false
      match idx with
      | some i => if (kids.drop (i + 1)).any (fun k => match k with
          | .node j kk => (j.cat == .PP || j.cat == .SBAR) && firstWordForm kk == some "as"
          | _ => false) then { asAs := 1 } else {}
      | none => {}
    let tag : Acc :=
      if !quoted && kids.any (fun k => match k with | .node j _ => j.cat == .QUOTE | _ => false) then
        match headVerb kids with
        | some w => if speechTagVerbs.contains (lemmaOf w) then { tags := [lemmaOf w] } else {}
        | none => {}
      else {}
    -- the subject passes down the head and conjuncts; the tense to every clause below
    -- without its own (as in `Complete.lean`), and a verb of saying makes what it says reported
    let saying := (verb.map fun w => speechTagVerbs.contains (lemmaOf w)).getD false
    let down (k : Tree) : Down :=
      let inherits := roleIs k .head || roleIs k .conj
      { subj := if inherits then subj else none,
        tense := tns, quoted, said := d.said || (saying && !inherits) }
    let below := kids.foldl (fun a k => a.add (accOf cx (down k) k)) {}
    [here, prn, like, asif, asas, tag].foldl Acc.add below

/-- Capitalised common nouns, skipping a capital's usual positions. -/
def conceptCount (ws : List Word) : Nat :=
  (ws.foldl (fun (n, prev) w =>
    let initial := match prev with
      | none => true
      | some p => capAfter.contains p
    let cap := match w.form.toList.head? with | some c => c.isUpper | none => false
    let n := if w.upos == .NOUN && cap && !initial then n + 1 else n
    (n, if w.upos == .PUNCT || w.upos == .SYM then some w.form else
      if isWord w then some "" else prev))
    (0, (none : Option String))).1

/-- Read one sentence. -/
def sentOf (cx : Ctx) (para : Nat) (t : Tree) : Sent :=
  let ls := leaves t
  let rootKids := match t with | .node _ kk => kk | .leaf _ => []
  let isFoot : Bool := match t with
    | .node i (.leaf w :: _) => i.cat == Cat.PRN && w.upos == UPOS.SYM && footMarks.contains w.form
    | _ => false
  let footMark := if isFoot then (ls.head?.map (·.form)) else none
  let anchors := rootKids.filterMap fun k => match k with
    | .leaf w => if w.upos == .SYM && w.role == some .dep && footMarks.contains w.form then some w.form else none
    | _ => none
  let a : Acc := accOf cx {} t
  -- without its marks: a clause somewhere, and the last leaf terminal punctuation
  let rest := ls.filter fun w => !(w.upos == .SYM && footMarks.contains w.form)
  let whole := anchors.isEmpty ||
    (a.clauses > 0 && match rest.getLast? with
      | some w => terminalPunct.contains w.form | none => false)
  let opener := (ls.find? isWord).bind fun w =>
    if (w.role.map connectiveRoles.contains).getD false &&
       (w.upos == .CCONJ || w.upos == .ADV || w.upos == .SCONJ) then some (lower w.form) else none
  { para, words := (ls.filter isWord).length, depth := depth t,
    prn := if isFoot then a.prn - 1 else a.prn,
    anchors, footnote := footMark, wholeWithout := whole,
    clauses := a.clauses, generics := a.generics, likeSimiles := a.likeSimiles, asIf := a.asIf,
    asAs := a.asAs, concepts := conceptCount ls, quoteWords := a.quoteWords, tags := a.tags,
    opener, interior := a.interior, choreo := a.choreo, povClauses := a.povClauses }

/-- Read a paragraph's document. -/
def sentsOfDoc (cx : Ctx) (para : Nat) (d : Doc) : List Sent :=
  let cx := if cx.paper then { cx with specific := (d.entities.filter (!·.generic)).map (·.id) } else cx
  d.sentences.map fun s => sentOf cx para s.tree

/-! ## A story's features -/

/-- Distinct elements, by structural recursion (kernel-friendly). -/
def distinct : List String → List String
  | [] => []
  | x :: xs => let r := distinct xs; if r.contains x then r else x :: r

def sumBy (f : Sent → Nat) : List Sent → Nat
  | [] => 0
  | s :: ss => f s + sumBy f ss

def countIf (p : Sent → Bool) : List Sent → Nat
  | [] => 0
  | s :: ss => (if p s then 1 else 0) + countIf p ss

/-- Every anchor has exactly one footnote with its mark later in its paragraph,
every footnote exactly one anchor earlier, and the anchor's sentence is whole
without its marks. -/
def footnotesPaired (ss : List Sent) : Bool :=
  let idx := ss.zipIdx
  idx.all fun (s, i) =>
    s.wholeWithout &&
    (s.anchors.all fun m =>
      (idx.filter fun (t, j) => j > i && t.para == s.para && t.footnote == some m).length == 1 &&
      (s.anchors.filter (· == m)).length == 1) &&
    (match s.footnote with
      | some m => (idx.filter fun (t, j) => j < i && t.para == s.para && t.anchors.contains m).length == 1
      | none => true)

/-- Every footnote says something general: it contains a generic clause. -/
def footnotesGeneric (ss : List Sent) : Bool :=
  ss.all fun s => s.footnote.isNone || s.generics > 0

/-- A story's style features: counts, so that every ratio is a cross-multiplication. -/
structure Features where
  paras : Nat
  sents : Nat
  words : Nat
  clauses : Nat
  depthSum : Nat
  maxDepth : Nat
  /-- sentences of at most 6 words -/
  short : Nat
  /-- sentences of at least 25 words -/
  long : Nat
  prn : Nat
  anchors : Nat
  footnotes : Nat
  footnoteWords : Nat
  generics : Nat
  likeSimiles : Nat
  asIf : Nat
  asAs : Nat
  concepts : Nat
  quoteWords : Nat
  tags : Nat
  tagKinds : Nat
  /-- tags that are not "say" -/
  fancyTags : Nat
  openers : Nat
  openerKinds : Nat
  interior : Nat
  choreo : Nat
  povClauses : Nat
  /-- narrator asides: generic clauses, parentheticals and footnotes -/
  asides : Nat
  footPaired : Bool
  footGeneric : Bool
  deriving Repr, DecidableEq, Inhabited

def Features.ofSents (ss : List Sent) : Features :=
  let tags := ss.flatMap (·.tags)
  let openers := ss.filterMap (·.opener)
  let generics := sumBy (·.generics) ss
  let prn := sumBy (·.prn) ss
  let footnotes := countIf (·.footnote.isSome) ss
  { paras := (distinct (ss.map fun s => toString s.para)).length
    sents := ss.length
    words := sumBy (·.words) ss
    clauses := sumBy (·.clauses) ss
    depthSum := sumBy (·.depth) ss
    maxDepth := (ss.map (·.depth)).foldl max 0
    short := countIf (·.words ≤ 6) ss
    long := countIf (·.words ≥ 25) ss
    prn
    anchors := sumBy (·.anchors.length) ss
    footnotes
    footnoteWords := sumBy (fun s => if s.footnote.isSome then s.words else 0) ss
    generics
    likeSimiles := sumBy (·.likeSimiles) ss
    asIf := sumBy (·.asIf) ss
    asAs := sumBy (·.asAs) ss
    concepts := sumBy (·.concepts) ss
    quoteWords := sumBy (·.quoteWords) ss
    tags := tags.length
    tagKinds := (distinct tags).length
    fancyTags := (tags.filter (· != "say")).length
    openers := openers.length
    openerKinds := (distinct openers).length
    interior := sumBy (·.interior) ss
    choreo := sumBy (·.choreo) ss
    povClauses := sumBy (·.povClauses) ss
    asides := generics + prn + footnotes
    footPaired := footnotesPaired ss
    footGeneric := footnotesGeneric ss }

/-- A numeric feature, by name. -/
inductive Feat where
  | paras | sents | words | clauses | depthSum | maxDepth | short | long | prn | anchors
  | footnotes | footnoteWords | generics | likeSimiles | asIf | asAs | similes | concepts
  | quoteWords | tags | tagKinds | fancyTags | openers | openerKinds | interior | choreo | povClauses | charClauses | asides
  deriving Repr, DecidableEq, Inhabited

def Features.get (f : Features) : Feat → Nat
  | .paras => f.paras | .sents => f.sents | .words => f.words | .clauses => f.clauses
  | .depthSum => f.depthSum | .maxDepth => f.maxDepth | .short => f.short | .long => f.long
  | .prn => f.prn | .anchors => f.anchors | .footnotes => f.footnotes
  | .footnoteWords => f.footnoteWords | .generics => f.generics
  | .likeSimiles => f.likeSimiles | .asIf => f.asIf | .asAs => f.asAs
  | .similes => f.likeSimiles + f.asIf + f.asAs | .concepts => f.concepts
  | .quoteWords => f.quoteWords | .tags => f.tags | .tagKinds => f.tagKinds
  | .fancyTags => f.fancyTags | .openers => f.openers | .openerKinds => f.openerKinds
  | .interior => f.interior | .choreo => f.choreo | .povClauses => f.povClauses
  | .charClauses => f.interior + f.choreo | .asides => f.asides

def Feat.name : Feat → String
  | .paras => "paras" | .sents => "sents" | .words => "words" | .clauses => "clauses"
  | .depthSum => "depthSum" | .maxDepth => "maxDepth" | .short => "short" | .long => "long"
  | .prn => "prn" | .anchors => "anchors" | .footnotes => "footnotes"
  | .footnoteWords => "footnoteWords" | .generics => "generics" | .likeSimiles => "likeSimiles"
  | .asIf => "asIf" | .asAs => "asAs" | .similes => "similes" | .concepts => "concepts"
  | .quoteWords => "quoteWords" | .tags => "tags" | .tagKinds => "tagKinds"
  | .fancyTags => "fancyTags" | .openers => "openers" | .openerKinds => "openerKinds"
  | .interior => "interior" | .choreo => "choreo" | .povClauses => "povClauses"
  | .charClauses => "charClauses" | .asides => "asides"

def Feat.all : List Feat :=
  [.paras, .sents, .words, .clauses, .depthSum, .maxDepth, .short, .long, .prn, .anchors,
   .footnotes, .footnoteWords, .generics, .likeSimiles, .asIf, .asAs, .similes, .concepts,
   .quoteWords, .tags, .tagKinds, .fancyTags, .openers, .openerKinds, .interior, .choreo, .povClauses, .charClauses, .asides]

/-! ## Rules and styles -/

/-- One decidable rule over a story's features. -/
inductive Rule where
  | atLeast (f : Feat) (n : Nat)
  | atMost (f : Feat) (n : Nat)
  /-- `num / den ≥ p / q`, as `num * q ≥ p * den` -/
  | ratioAtLeast (num den : Feat) (p q : Nat)
  /-- `num / den ≤ p / q`, as `num * q ≤ p * den` -/
  | ratioAtMost (num den : Feat) (p q : Nat)
  /-- every footnote is anchored once, and its anchor's sentence is whole without it -/
  | footnotesPaired
  /-- every footnote contains a generic statement -/
  | footnotesGeneric
  deriving Repr, DecidableEq, Inhabited

def Rule.holds (f : Features) : Rule → Bool
  | .atLeast x n => f.get x ≥ n
  | .atMost x n => f.get x ≤ n
  | .ratioAtLeast a b p q => f.get a * q ≥ p * f.get b
  | .ratioAtMost a b p q => f.get a * q ≤ p * f.get b
  | .footnotesPaired => f.footPaired
  | .footnotesGeneric => f.footGeneric

def Rule.show : Rule → String
  | .atLeast x n => s!"{x.name} ≥ {n}"
  | .atMost x n => s!"{x.name} ≤ {n}"
  | .ratioAtLeast a b p q => s!"{a.name} / {b.name} ≥ {p}/{q}"
  | .ratioAtMost a b p q => s!"{a.name} / {b.name} ≤ {p}/{q}"
  | .footnotesPaired => "every footnote anchored once, its sentence whole without it"
  | .footnotesGeneric => "every footnote generalises"

/-- A style: named decidable rules. -/
structure Style where
  name : String
  rules : List (String × Rule)

/-- The names of the rules the features break. -/
def Style.failing (st : Style) (f : Features) : List String :=
  (st.rules.filter fun (_, r) => !r.holds f).map (·.1)

def Style.holds (st : Style) (f : Features) : Bool := st.failing f |>.isEmpty

end LangLib.Style
