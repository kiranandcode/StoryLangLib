/-!
# Core datatypes

Three layers over one text:

* token layer: the surface words and punctuation, in order;
* syntax layer: a constituency tree whose leaves are the tokens, each tagged
  with a Universal Dependencies part of speech, and whose edges carry a UD
  grammatical relation;
* reference layer: constituents and words point at entities declared once per
  document, so anaphora (backward) and cataphora (forward) are links to the same
  entity, classified by position.

Rendering a tree is reading its leaves left to right, so word order lives in the
tree itself and a faithful encoding must reproduce the source tokens exactly.
-/

namespace LangLib

/-- Universal Dependencies v2 universal part-of-speech tags. -/
inductive UPOS where
  | ADJ | ADP | ADV | AUX | CCONJ | DET | INTJ | NOUN | NUM | PART
  | PRON | PROPN | PUNCT | SCONJ | SYM | VERB | X
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace UPOS
def all : List UPOS :=
  [ADJ, ADP, ADV, AUX, CCONJ, DET, INTJ, NOUN, NUM, PART,
   PRON, PROPN, PUNCT, SCONJ, SYM, VERB, X]

def name : UPOS → String
  | ADJ => "ADJ" | ADP => "ADP" | ADV => "ADV" | AUX => "AUX"
  | CCONJ => "CCONJ" | DET => "DET" | INTJ => "INTJ" | NOUN => "NOUN"
  | NUM => "NUM" | PART => "PART" | PRON => "PRON" | PROPN => "PROPN"
  | PUNCT => "PUNCT" | SCONJ => "SCONJ" | SYM => "SYM" | VERB => "VERB"
  | X => "X"

def ofString? (s : String) : Option UPOS := all.find? (·.name == s)
end UPOS

/-- Phrase categories (Penn-style constituents, plus a few for literary text). -/
inductive Cat where
  /-- a clause -/
  | S
  /-- a clause introduced by a subordinator or relative -/
  | SBAR
  | NP | VP | PP | ADJP | ADVP
  /-- coordination of like constituents -/
  | COORD
  /-- quoted speech or thought; may carry a speaker -/
  | QUOTE
  /-- a parenthetical or dash-delimited aside -/
  | PRN
  /-- interjection, vocative or other discourse material -/
  | INTJ
  /-- anything that is not a full clause: headlines, fragments, ellipsis -/
  | FRAG
  deriving Repr, DecidableEq, Inhabited

namespace Cat
def all : List Cat := [S, SBAR, NP, VP, PP, ADJP, ADVP, COORD, QUOTE, PRN, INTJ, FRAG]

def name : Cat → String
  | S => "S" | SBAR => "SBAR" | NP => "NP" | VP => "VP" | PP => "PP"
  | ADJP => "ADJP" | ADVP => "ADVP" | COORD => "COORD" | QUOTE => "QUOTE"
  | PRN => "PRN" | INTJ => "INTJ" | FRAG => "FRAG"

def ofString? (s : String) : Option Cat := all.find? (·.name == s)
end Cat

/-- The grammatical relation of a constituent to its parent: UD v2 relations,
plus `head` for the head child of a phrase. -/
inductive Role where
  | head | root
  | nsubj | csubj | obj | iobj | obl | expl
  | ccomp | xcomp | advcl | acl | relcl
  | nmod | amod | advmod | nummod | appos | det | poss | case | mark
  | aux | cop | compound | flat | fixed
  | conj | cc | vocative | discourse | dislocated | parataxis
  | punct | dep
  deriving Repr, DecidableEq, Inhabited

namespace Role
def all : List Role :=
  [head, root, nsubj, csubj, obj, iobj, obl, expl, ccomp, xcomp, advcl, acl,
   relcl, nmod, amod, advmod, nummod, appos, det, poss, case, mark, aux, cop,
   compound, flat, fixed, conj, cc, vocative, discourse, dislocated, parataxis,
   punct, dep]

def name : Role → String
  | head => "head" | root => "root" | nsubj => "nsubj" | csubj => "csubj"
  | obj => "obj" | iobj => "iobj" | obl => "obl" | expl => "expl"
  | ccomp => "ccomp" | xcomp => "xcomp" | advcl => "advcl" | acl => "acl"
  | relcl => "relcl" | nmod => "nmod" | amod => "amod" | advmod => "advmod"
  | nummod => "nummod" | appos => "appos" | det => "det" | poss => "poss"
  | case => "case" | mark => "mark" | aux => "aux" | cop => "cop"
  | compound => "compound" | flat => "flat" | fixed => "fixed"
  | conj => "conj" | cc => "cc" | vocative => "vocative"
  | discourse => "discourse" | dislocated => "dislocated"
  | parataxis => "parataxis" | punct => "punct" | dep => "dep"

def ofString? (s : String) : Option Role := all.find? (·.name == s)
end Role

abbrev EntityId := String

/-- A surface token with its analysis. `form` must be exactly one token of the
source text, as cut by `LangLib.tokenize`. -/
structure Word where
  form : String
  upos : UPOS
  role : Option Role := none
  lemma : Option String := none
  /-- UD morphological features, e.g. `("Number", "Plur")`. -/
  feats : List (String × String) := []
  /-- the entity this word mentions (pronouns, bare names) -/
  ref : Option EntityId := none
  deriving Repr, Inhabited

/-- Annotation on a phrase node. -/
structure NodeInfo where
  cat : Cat
  role : Option Role := none
  /-- the entity this constituent mentions (typically an NP) -/
  ref : Option EntityId := none
  /-- for `QUOTE`: who says or thinks it -/
  speaker : Option EntityId := none
  deriving Repr, Inhabited

inductive Tree where
  | leaf (w : Word)
  | node (info : NodeInfo) (kids : List Tree)
  deriving Repr, Inhabited

inductive EntityKind where
  | person | group | animal | object | place | time | event | abstract
  deriving Repr, DecidableEq, Inhabited

namespace EntityKind
def all : List EntityKind := [person, group, animal, object, place, time, event, abstract]
def name : EntityKind → String
  | person => "person" | group => "group" | animal => "animal"
  | object => "object" | place => "place" | time => "time"
  | event => "event" | abstract => "abstract"
def ofString? (s : String) : Option EntityKind := all.find? (·.name == s)
end EntityKind

/-- Which third-person pronoun series refers to an entity. -/
inductive PronSeries where
  | he | she | it | they
  deriving Repr, DecidableEq, Inhabited

namespace PronSeries
def all : List PronSeries := [he, she, it, they]
def name : PronSeries → String
  | he => "he" | she => "she" | it => "it" | they => "they"
def ofString? (s : String) : Option PronSeries := all.find? (·.name == s)
end PronSeries

structure Entity where
  id : EntityId
  name : String
  kind : EntityKind := .person
  pron : Option PronSeries := none
  deriving Repr, Inhabited

/-- A topic the text is about, linking the entities that make it up. -/
structure Topic where
  id : String
  label : String
  entities : List EntityId := []
  deriving Repr, Inhabited

/-- A sentence: its tree, plus an optional link to a topic. -/
structure Sentence where
  tree : Tree
  topic : Option String := none
  deriving Repr, Inhabited

structure Doc where
  entities : List Entity := []
  topics : List Topic := []
  sentences : List Sentence := []
  deriving Repr, Inhabited

end LangLib
