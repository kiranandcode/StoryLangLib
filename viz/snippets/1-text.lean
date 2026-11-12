-- LangLib/Basic.lean : one document, three layers
inductive UPOS  | ADJ | ADP | ADV | AUX | CCONJ | DET | INTJ | NOUN | NUM | PART
                | PRON | PROPN | PUNCT | SCONJ | SYM | VERB | X
inductive Cat   | S | SBAR | NP | VP | PP | ADJP | ADVP | COORD | QUOTE | PRN | INTJ | FRAG
inductive Role  | head | root | nsubj | obj | iobj | obl | advcl | amod | det | case
                | mark | aux | cc | conj | vocative | punct | ...      -- UD v2 relations

structure Word where                 -- a surface token and its analysis
  form  : String                     -- exactly one token of the source
  upos  : UPOS
  role  : Option Role := none
  lemma : Option String := none
  feats : List (String × String) := []
  ref   : Option EntityId := none    -- the entity this word mentions

structure NodeInfo where
  cat : Cat
  role : Option Role := none
  ref : Option EntityId := none      -- the entity this phrase mentions
  speaker : Option EntityId := none  -- on QUOTE: who says it

inductive Tree where
  | leaf (w : Word)
  | node (info : NodeInfo) (kids : List Tree)

structure Entity where
  id : EntityId;  name : String;  kind : EntityKind;  pron : Option PronSeries

structure Doc where
  entities : List Entity;  topics : List Topic;  sentences : List Sentence

-- LangLib/Render.lean : pretty printing is reading the leaves in order
def Tree.render : Tree → List String
theorem Tree.render_node (i : NodeInfo) (kids : List Tree) :
    (Tree.node i kids).render = (kids.map Tree.render).flatten

-- LangLib/Check.lean : the anti-hallucination gate
def check (text : String) (d : Doc) : CheckResult
  -- ok  ⇔  tokenDiff (tokenize text) d.render = []  ∧  every leaf is one token
  --        ∧  every ref resolves, pronouns agree, no 3rd-person pronoun unresolved
