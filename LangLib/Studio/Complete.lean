import LangLib.Studio.Report
import LangLib.World.Cause

/-!
# Completeness: every part of the tree is a judgement from the world

A paragraph's annotation is a tree; its reading says what happens. The
setting already holds every noun to the world (a ref or a sense). This file
does the same for the rest of the tree, closed-world:

* **Predications.** Every clause (a verb heading its node, or a copula) carries
  at least one judgement anchored at its head word, and each judgement holds:
  - `event`: one of the paragraph's events (it is valid where it stands, as the
    report already checks), whose arguments include every world thing the
    clause's subject, object and obliques refer to;
  - `claim`: a claim about the state, true at that point;
  - `content`: the clause is the content of its parent clause's belief or
    speech ("he told himself *Gallery Fake was still up*"): the parent is
    judged by a mind event or belief claim with exactly this literal;
  - `goal`: a purpose clause ("to hide"): the agent of the event it is the
    purpose of wants it at that point;
  - `act`: a gesture with no other world content ("Hisoka smiled"): its subject
    is a character on stage;
  - `speech`: words said, in a quote or as what a verb of saying says;
  - `hypothetical`: under a modal or a condition ("could", "if", "as if");
  - `external`: a move checked in another file (the fight's Nen moves), whose
    world ids include the clause's.
  A negated clause cannot assert an event, unless the event's literal is itself
  negative ("Chrollo was not there": Hisoka notices he is not).
* **Connectives**, read off the tree: "then", "after", "once", "when" (the
  second after the first), "before", "until", "while", "meanwhile" (time,
  checked on the order of the judgements); "because", "since", "so" (cause:
  `World/Cause.lean`; a "since" marked `"sense": "time"` is time order);
  "to", "in order to", "so that" (purpose: the clause is judged `goal`);
  "though", "although" (both hold); "if", "as if", "unless", "whether" (the
  dependent clause is hypothetical).
* **Modifiers** on people and events: an adjective said of a character is one
  of their traits or marked `impression`; an adverb on a clause is a connective
  or negation the model reads, or carries a sense (`impression`, `manner`,
  `degree`, `direction`, `place`, `time`, `order`, `aspect`).

`completeIssues` lists what fails, in words; `TreeFacts` (what the tree says,
read by `treeFacts`) and the judgements are data, so a story's Lean file
restates the verdict and proves it by `decide`.
-/

namespace LangLib.Studio
open LangLib LangLib.World LangLib.Scene

/-- A world thing a word refers to. -/
inductive WId | ch (i : Nat) | pl (i : Nat) | ob (i : Nat)
  deriving DecidableEq, Repr

inductive LinkRel | cause | effect | purpose | after | before | during | concession | condition
  deriving DecidableEq, Repr

/-- A clause: a verb heading its node, or a copula. -/
structure Pred where
  at_ : Nat
  lemma : String
  subj : Option WId := none
  /-- world things its object, indirect object and obliques refer to -/
  args : List WId := []
  neg : Bool := false
  modal : Bool := false
  quoted : Bool := false
  /-- what a verb of saying says -/
  said : Bool := false
  parent : Option Nat := none
  parentLemma : String := ""
  /-- the clause's own words (its subject first; embedded clauses left out) -/
  text : String := ""
  /-- its subject, when that is a thing of the setting (a fixture or scenery) -/
  thing : Option Spot := none
  /-- the kinds of fact its subject, object and obliques name ("weather", "light", "sound") -/
  kinds : List String := []
  deriving DecidableEq, Repr

/-- A connective: `rel` holds between the clause it introduces (`a`) and the
clause it attaches to (`b`). -/
structure Link where
  at_ : Nat
  word : String
  rel : LinkRel
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

/-- A modifier the world must account for. -/
structure Modifier where
  at_ : Nat
  word : String
  /-- the character an adjective is said of -/
  of : Option Nat := none
  sense : Option String := none
  deriving DecidableEq, Repr

structure TreeFacts where
  preds : List Pred := []
  links : List Link := []
  mods : List Modifier := []
  deriving DecidableEq, Repr, Inhabited

inductive JKind where
  /-- the paragraph's `i`-th event -/
  | event (i : Nat)
  | claim (c : Claim)
  | content (l : Fact × Bool)
  | goal (l : Fact × Bool)
  | act | speech | hypothetical
  | external (ids : List WId)
  deriving DecidableEq, Repr

structure Judge where
  at_ : Nat
  kind : JKind
  deriving DecidableEq, Repr

def modSenses : List String :=
  ["impression", "manner", "degree", "direction", "place", "time", "order", "aspect"]

def speechVerbs : List String :=
  ["say", "tell", "ask", "answer", "order", "command", "give", "shout", "whisper", "call",
   "explain", "announce", "reply"]

def negWords : List String := ["not", "n't", "never", "no", "nothing", "nobody", "none", "neither", "nor"]
def modalWords : List String := ["would", "could", "might", "may", "should", "can", "must"]

/-- What a subordinator says. -/
def LinkRel.ofMarker : String → Option LinkRel
  | "because" | "since" | "for" => some .cause
  | "so" => some .effect
  | "to" | "in order to" | "so that" | "so as to" => some .purpose
  | "after" | "once" | "when" | "as soon as" => some .after
  | "before" | "until" | "till" => some .before
  | "while" | "as" | "as long as" | "whilst" => some .during
  | "though" | "although" | "even though" | "even if" => some .concession
  | "if" | "as if" | "unless" | "whether" | "as though" => some .condition
  | _ => none

/-- Adverbs that relate a clause to the one before it. -/
def LinkRel.ofAdverb : String → Option LinkRel
  | "then" | "later" | "afterwards" | "next" => some .after
  | "meanwhile" => some .during
  | "earlier" => some .before
  | _ => none

/-! ## Reading the tree -/

section
variable (s : Spec) (R : Resolver (Ch s) (Pl s) (Ob s))

private def roleIs (t : Tree) (r : Role) : Bool := match t with
  | .leaf w => w.role == some r
  | .node i _ => i.role == some r

private def refOf : Tree → Option EntityId
  | .leaf w => w.ref
  | .node i kids => i.ref <|> (kids.findSome? fun
      | .node j _ => if j.cat == .NP then j.ref else none
      | .leaf w => w.ref)

def wid (e : EntityId) : Option WId :=
  (R.char e).map (fun c => .ch c.i) <|> (R.place e).map (fun p => .pl p.i) <|>
    (R.obj e).map (fun o => .ob o.i)

private def lower (w : Word) : String := w.form.toLower

/-- The head token of a node: where its clause is, or its head child's. -/
partial def headAt : Tree → Nat → Option Nat
  | .leaf _, _ => none
  | .node _ kids, start =>
    let offs := (kids.foldl (fun (acc, p) k => (acc ++ [p], p + k.render.length)) (([] : List Nat), start)).1
    let placed := kids.zip offs
    let verb := placed.findSome? fun (k, o) => match k with
      | .leaf w => if w.upos == .VERB && w.role == some .head then some o else none
      | _ => none
    let cop := placed.findSome? fun (k, o) => if roleIs k .cop then some o else none
    let headK := placed.find? fun (k, _) => roleIs k .head
    match verb, cop with
    | some o, _ => some o
    | none, some c => some ((headK.map (·.2)).getD c)
    | none, none => headK.bind fun (k, o) => headAt k o

/-- Senses that name a kind of fact a clause must then be judged by. -/
def factSenses : List String := ["weather", "light", "sound"]

/-- The sense of a phrase's head noun. -/
private partial def headSense : Tree → Option String
  | .leaf w => if w.upos == .NOUN then w.sense else none
  | .node i kids => i.sense <|> kids.findSome? fun k =>
    match k with
    | .leaf w => if w.role == some .head || w.role == some .conj then headSense k else none
    | .node j _ => if j.role == some .head || j.role == some .conj then headSense k else none

/-- Words of a node's direct children, outside any clause below it. -/
private partial def shallowLeaves : Tree → List Word
  | .leaf w => [w]
  | .node i kids => if i.cat == .S || i.cat == .SBAR then [] else kids.flatMap shallowLeaves

structure TCtx where
  subj : Option WId := none
  parent : Option Nat := none
  parentLemma : String := ""
  quoted : Bool := false
  cond : Bool := false
  said : Bool := false
  /-- the words of the nearest subject above -/
  subjTxt : String := ""
  /-- the nearest subject above, when it is a thing of the setting -/
  subjThing : Option Spot := none

/-- Roles of children that are clauses of their own (left out of a clause's words). -/
def clauseRoles : List Role := [.advcl, .ccomp, .xcomp, .relcl, .acl, .conj, .parataxis, .appos, .csubj]

/-- A clause's own words: its leaves, minus punctuation and the clauses inside it. -/
partial def ownWords : Tree → List String
  | .leaf w => if w.upos == .PUNCT then [] else [w.form]
  | .node _ kids => kids.flatMap fun k => match k with
    | .node ki _ =>
      if ki.cat == .S || ki.cat == .SBAR || (ki.role.map clauseRoles.contains).getD false then [] else ownWords k
    | .leaf _ => ownWords k

/-- Clauses, connectives and modifiers of a tree starting at token `start`. -/
partial def factsOf (ctx : TCtx) : Tree → Nat → TreeFacts
  | .leaf _, _ => {}
  | t@(.node info kids), start =>
    let offs := (kids.foldl (fun (acc, p) k => (acc ++ [p], p + k.render.length)) (([] : List Nat), start)).1
    let placed := kids.zip offs
    let quoted := ctx.quoted || info.cat == .QUOTE
    let subj := if info.cat == .S || info.cat == .SBAR || info.cat == .VP then
        ((kids.find? (roleIs · .nsubj)).bind refOf |>.bind (wid s R)) <|> ctx.subj
      else ctx.subj
    let thingOf (k : Tree) : Option Spot := (refOf k).bind fun e => match s.names.spot? e with
      | some (.thing t) => some (.thing t) | _ => none
    let subjThing := if info.cat == .S || info.cat == .SBAR || info.cat == .VP then
        match kids.find? (roleIs · .nsubj) with
        | some k => thingOf k
        | none => ctx.subjThing
      -- a clause hanging off a noun phrase ("the printers ticking") is about that phrase
      else if info.cat == .NP then thingOf t <|> ctx.subjThing
      else ctx.subjThing
    let verb := placed.findSome? fun (k, o) => match k with
      | .leaf w => if w.upos == .VERB && w.role == some .head then some (o, w) else none
      | _ => none
    let cop := placed.findSome? fun (k, o) => if roleIs k .cop then some o else none
    let me : Option Pred := match verb, cop with
      | some (o, w), _ => some { at_ := o, lemma := (w.lemma.getD w.form).toLower, subj }
      | none, some c =>
        let h := (placed.find? fun (k, _) => roleIs k .head)
        some { at_ := (h.map (·.2)).getD c, lemma := "be", subj }
      | none, none => none
    let nsubjK := kids.find? (roleIs · .nsubj)
    let subjTxt := match nsubjK with
      | some k => " ".intercalate (ownWords k)
      | none => ctx.subjTxt
    let me := me.map fun p =>
      let near := kids.flatMap shallowLeaves
      let own := " ".intercalate (ownWords t)
      { p with
        text := if nsubjK.isSome || subjTxt.isEmpty then own else s!"{subjTxt} {own}",
        thing := subjThing,
        kinds := ((kids.filter fun k => roleIs k .nsubj || roleIs k .obj || roleIs k .iobj || roleIs k .obl).filterMap
          headSense).filter factSenses.contains |>.eraseDups,
        args := (kids.filter fun k => roleIs k .obj || roleIs k .iobj || roleIs k .obl).filterMap
          (fun k => (refOf k).bind (wid s R)),
        neg := near.any fun w => negWords.contains (lower w),
        modal := ctx.cond || near.any fun w => w.upos == .AUX && modalWords.contains (lower w),
        quoted, said := ctx.said, parent := ctx.parent, parentLemma := ctx.parentLemma }
    let ctx' : TCtx := match me with
      | some p => { subj, parent := some p.at_, parentLemma := p.lemma, quoted, cond := p.modal,
                    said := ctx.said || speechVerbs.contains p.lemma, subjTxt, subjThing }
      | none => { ctx with subj, quoted, subjTxt, subjThing }
    let hereAt := headAt t start
    -- connectives introduced by subordinate clauses, "so", and relating adverbs
    let links : List Link := placed.filterMap fun (k, o) =>
      match k with
      | .node ki kk =>
        if ki.role == some .advcl then
          let koffs := (kk.foldl (fun (acc, p) x => (acc ++ [p], p + x.render.length)) (([] : List Nat), o)).1
          let marks := (kk.zip koffs).filter fun (x, _) => match x with
            | .leaf w => w.role == some .mark || w.role == some .fixed ||
                (w.role == some .advmod && (w.upos == .ADV) &&
                  kk.any (fun y => roleIs y .mark))
            | _ => false
          let phrase := " ".intercalate (marks.map fun (x, _) => match x with
            | .leaf w => lower w | _ => "")
          -- "since" marked `"sense": "time"` is temporal, not causal ("since he was nine"); a
          -- temporal "as" already reads as at the same time, and stays so
          let temporal := marks.any fun (x, _) => match x with
            | .leaf w => w.sense == some "time" | _ => false
          let rel := (LinkRel.ofMarker phrase).map fun r =>
            if temporal && r == .cause then LinkRel.after else r
          match rel, marks.head?, headAt k o, hereAt with
          | some r, some (_, mo), some a, some b => some { at_ := mo, word := phrase, rel := r, a, b }
          | _, _, _, _ => none
        else if ki.role == some .conj then
          match kk.head?, headAt k o, hereAt with
          | some (.leaf w), some a, _ =>
            if w.role == some .cc && lower w == "so" then
              -- the previous conjunct is the cause, this one the effect
              (placed.filter fun (x, xo) => xo < o && (roleIs x .head)).getLast?.bind fun (x, xo) =>
                (headAt x xo).map fun c => { at_ := o, word := "so", rel := .cause, a := c, b := a }
            else none
          | _, _, _ => none
        else none
      | .leaf w =>
        if w.role == some .advmod then
          match LinkRel.ofAdverb (lower w), hereAt with
          -- `a` is filled in later: the clause before this node
          | some r, some b => some { at_ := o, word := lower w, rel := r, a := start, b }
          | _, _ => none
        else none
    let condHere := links.any fun l => l.rel == .condition
    -- "whether" or "if" heading a complement makes it hypothetical too
    let condComp := info.cat == .SBAR && kids.any fun k => match k with
      | .leaf w => w.role == some .mark && ["whether", "if"].contains (lower w)
      | _ => false
    -- modifiers: adjectives on characters, adverbs on clauses
    let refHere := (info.ref.bind (wid s R)) <|>
      ((placed.findSome? fun (k, _) => match k with
        | .leaf w => if w.role == some .head then w.ref.bind (wid s R) else none
        | _ => none))
    let markerAts := links.map (·.at_)
    let mods : List Modifier := placed.filterMap fun (k, o) => match k with
      | .leaf w =>
        if w.upos == .ADJ && w.role == some .amod && info.cat == .NP then
          match refHere with
          | some (WId.ch c) => some { at_ := o, word := (w.lemma.getD w.form).toLower, of := some c, sense := w.sense }
          | _ => none
        else if (w.upos == .ADV) && w.role != some .head && w.role != some .mark &&
            w.role != some .fixed && !negWords.contains (lower w) &&
            (LinkRel.ofAdverb (lower w)).isNone && !markerAts.contains o &&
            !(info.role == some .advcl && w.role == some .advmod && kids.any (roleIs · .mark)) &&
            !(info.cat == .SBAR && ["where", "when", "why", "how"].contains (lower w)) then
          some { at_ := o, word := lower w, sense := w.sense <|> info.sense }
        else none
      | .node _ _ => none
    -- a node that is not a clause but has a head clause: its other children depend on that clause
    -- ("He saw the plan at once: Chrollo would hide behind the man")
    let headLemma : Option String := hereAt.bind fun h => placed.findSome? fun (k, o) =>
      if headAt k o == some h then match k with
        | .leaf w => some (w.lemma.getD w.form).toLower
        | .node _ kk => (kk.findSome? fun x => match x with
            | .leaf w => if w.role == some .head && w.upos == .VERB then some (w.lemma.getD w.form).toLower else none
            | _ => none)
      else none
    let inner := placed.foldl (fun (acc : TreeFacts) (k, o) =>
      let ctx' := if me.isSome || headAt k o == hereAt then ctx' else match hereAt with
        | some h =>
          let said := ctx'.said || speechVerbs.contains (headLemma.getD "")
          { ctx' with parent := some h, parentLemma := headLemma.getD "", said }
        | none => ctx'
      let c := { ctx' with cond := ctx'.cond || condComp || (condHere && roleIs k .advcl) }
      let f := factsOf c k o
      { preds := acc.preds ++ f.preds, links := acc.links ++ f.links, mods := acc.mods ++ f.mods }) {}
    { preds := me.toList ++ inner.preds, links := links ++ inner.links, mods := mods ++ inner.mods }
end

/-- What the tree of a document says needs judging. An adverb that relates a
clause to "the one before" is tied to the last clause before its sentence. -/
def treeFacts (s : Spec) (d : Doc) : TreeFacts :=
  let R := resolverOf s d
  let (f, _, starts) := d.sentences.foldl (fun ((acc : TreeFacts), p, ss) sn =>
    let g := factsOf s R {} sn.tree p
    ({ preds := acc.preds ++ g.preds, links := acc.links ++ g.links, mods := acc.mods ++ g.mods },
     p + sn.tree.render.length, ss ++ [p])) (({} : TreeFacts), 0, ([] : List Nat))
  let _ := starts
  let fix (l : Link) : Link :=
    if (LinkRel.ofAdverb l.word).isNone then l else
    -- `a` held the start of the adverb's node; the clause before is the last one before it
    match (f.preds.filter (·.at_ < l.a)).getLast? with
    | some p => { l with a := p.at_ }
    | none => { l with a := l.b }
  { f with preds := f.preds.mergeSort (fun x y => x.at_ ≤ y.at_), links := f.links.map fix }

/-! ## Judging -/

/-- World things a fact is about (an atom: the characters it declares). -/
def Fact.wids (s : Spec) : Fact → List WId
  | .at_ c p => [.ch c, .pl p] | .objAt o p => [.ob o, .pl p] | .holds c o => [.ch c, .ob o]
  | .did a b _ => [.ch a, .ch b]
  | .atom i => ((s.atoms[i]?).map fun a => a.who.map WId.ch).getD []

def Ev.wids (s : Spec) (e : Ev) : List WId :=
  e.parties.map (.ch ·) ++ match e with
    | .move _ p => [.pl p] | .take _ o | .drop _ o | .give _ _ o => [.ob o]
    | .tell _ _ l | .whisper _ _ l | .lie _ _ l | .notice _ l _ | .realise _ l | .answer _ _ l
    | .hint _ _ l | .sarcasm _ _ l | .promise _ _ l | .request _ _ l | .adopt _ l | .dropGoal _ l
    | .abandon _ l => Fact.wids s l.1
    | .ask _ _ f => Fact.wids s f
    | .make _ a _ | .become a _ => Fact.wids s (.atom a)
    | _ => []

def Claim.wids (s : Spec) : Claim → List WId
  | .thinks c l | .knows c l | .falseBelief c l | .goal c l => .ch c :: Fact.wids s l.1
  | .unaware c f => .ch c :: Fact.wids s f
  | .thinksThinks c d l => .ch c :: .ch d :: Fact.wids s l.1
  | .holdsTrue l => Fact.wids s l.1
  | .consented b a _ => [.ch b, .ch a]
  | .bond a b _ _ _ => [.ch a, .ch b]

/-- The literal a mind event or belief claim is about. -/
def Ev.content : Ev → Option (Fact × Bool)
  | .tell _ _ l | .whisper _ _ l | .lie _ _ l | .notice _ l _ | .realise _ l | .answer _ _ l
  | .hint _ _ l | .sarcasm _ _ l | .promise _ _ l | .request _ _ l => some l
  | _ => none

def Claim.content : Claim → Option (Fact × Bool)
  | .thinks _ l | .knows _ l | .falseBelief _ l | .thinksThinks _ _ l | .goal _ l | .holdsTrue l => some l
  | _ => none

def Ev.agent (e : Ev) : Option Nat := e.parties.head?

variable {s : Spec}

/-- The context of a paragraph: the events of the story before it (in the
order they take effect) and its own events with the tokens they are read at. -/
structure ParaCtx (s : Spec) where
  prior : List (E s)
  items : List (Ev × Nat)

namespace ParaCtx
variable (c : ParaCtx s)

/-- The paragraph's events read at tokens before `t`. -/
def before (t : Nat) : List (Ev × Nat) := c.items.filter (·.2 < t)

/-- The story up to token `t` of the paragraph. -/
def upToTok (t : Nat) : List (E s) := c.prior ++ (c.before t).map (Ev.toE s ·.1)

def stateAt (t : Nat) : W s := run s.start (c.upToTok t)

/-- The story up to and including the paragraph's `i`-th event, and its index there. -/
def upToItem (i : Nat) : List (E s) × Nat :=
  (c.prior ++ (c.items.take (i + 1)).map (Ev.toE s ·.1), c.prior.length + i)
end ParaCtx

/-- Where a judgement sits in time: an event at its place in the paragraph, any
other judgement between the events read before and after it. -/
def Judge.pos (c : ParaCtx s) (j : Judge) : Nat :=
  match j.kind with
  | .event i => 2 * i + 1
  | _ => 2 * (c.before j.at_).length

def judgesAt (js : List Judge) (t : Nat) : List Judge := js.filter (·.at_ == t)

/-- Does one judgement cause another (`World/Cause.lean`)? -/
def causes (c : ParaCtx s) (a b : Judge) : Bool :=
  match a.kind, b.kind with
  | .event i, .event j =>
    let (es, jj) := c.upToItem j
    let ii := c.prior.length + i
    enables s.start es ii jj ||
      motivates (C := Ch s) (Φ := SFact s) (E := A s) s.start es ii jj
  | .event i, .claim cl =>
    let es := c.upToTok b.at_
    bringsAbout s.start es (c.prior.length + i) es.length (fun w => cl.eval w)
  | .event i, .content l | .event i, .goal l =>
    let es := c.upToTok b.at_
    bringsAbout s.start es (c.prior.length + i) es.length (fun w => truthLit w (lit (s := s) l))
  | .claim _, .event j | .content _, .event j =>
    let l := match a.kind with | .claim cl => cl.content | .content l => some l | _ => none
    match l, ((c.items[j]?).bind (·.1.agent)) with
    | some l, some ag => (view (c.stateAt b.at_) (⟨ag⟩ : Ch s)).contains (lit l)
    | _, _ => false
  | .claim ca, .claim cb =>
    match ca.content, cb.content with
    | some la, some lb => loreCause (lit (s := s) la) (lit (s := s) lb)
    | _, _ => false
  | _, _ => false

def ParaCtx.holds (c : ParaCtx s) (j : Judge) : Bool :=
  match j.kind with
  | .claim cl => cl.eval (c.stateAt (j.at_ + 1))
  | _ => true

/-- A judgement of reported or imagined content: not a claim about the world. -/
def Judge.reported (j : Judge) : Bool :=
  match j.kind with | .content _ | .speech | .hypothetical => true | _ => false

/-- The fact ids a clause's judgements are about. -/
def judgedAtoms (c : ParaCtx s) (here : List Judge) : List Nat :=
  here.flatMap fun j => match j.kind with
    | .event i => ((c.items[i]?).map (·.1.atoms)).getD []
    | .claim cl => cl.atoms
    | _ => []

/-- A clause must be judged by facts about what it is about: a fact about its
subject when that is a thing of the setting, and a fact of each kind (weather,
light, sound) its nouns name. Reported clauses (speech, content, hypothetical)
are exempt: they are a character's words, not the world's. -/
def aboutIssues (c : ParaCtx s) (p : Pred) (here : List Judge) : List String :=
  if here.isEmpty || here.all Judge.reported then [] else
  let as := judgedAtoms c here
  let n := s.names
  -- a sound a character makes, read as their gesture, is the gesture
  let gesture := (match p.subj with | some (.ch _) => true | _ => false) && here.any (·.kind == .act)
  (match p.thing with
    | some t =>
      if as.any fun a => (s.atoms[a]?.bind (·.about)) == some t then [] else
      [s!"is about {n.spotS t}, but none of its judgements is a fact about it: read it as a claim or event " ++
        s!"about {n.spotS t} (a fact in story.json with \"about\": \"{n.spotS t}\")"]
    | none => []) ++
  (p.kinds.filterMap fun k =>
    if as.any (fun a => (s.atoms[a]?.map (·.kind)) == some k) || (k == "sound" && gesture) then none else
    some (s!"names {k}, but none of its judgements is a {k} fact: read it as a claim or event about one " ++
      s!"(a fact in story.json with \"kind\": \"{k}\")"))

/-- What is wrong with the paragraph's coverage, in words; empty when complete. -/
def completeIssues (c : ParaCtx s) (f : TreeFacts) (js : List Judge) (toks : List String) : List String :=
  let tok (t : Nat) : String := s!"'{toks.getD t "?"}' (token {t})"
  let predAts := f.preds.map (·.at_)
  let isTrait (ch : Nat) (word : String) : Bool :=
    match Trait.ofString? word, s.chars[ch]? with
    | some t, some cs => cs.traits.contains t
    | _, _ => false
  let stray := js.filterMap fun j =>
    if predAts.contains j.at_ then none
    else some s!"a judgement is anchored at {tok j.at_}, which heads no clause"
  let perPred := f.preds.flatMap fun p =>
    let here := judgesAt js p.at_
    if here.isEmpty then
      [s!"the clause at {tok p.at_} has no judgement: read it as an event, a claim, or say what it is " ++
        "(content, goal, act, speech, hypothetical)"]
    else
      let worldRefs := p.subj.toList ++ p.args
      -- the world things the clause mentions must be among those its judgements mention
      let ids : List WId := here.flatMap fun j => match j.kind with
        | .event i => ((c.items[i]?).map (Ev.wids s ·.1)).getD []
        | .claim cl => Claim.wids s cl
        | .external xs => xs
        | _ => []
      let worldJudged := here.any fun j => match j.kind with
        | .event _ | .claim _ | .external _ => true | _ => false
      let missing := worldRefs.filter (!ids.contains ·)
      (if worldJudged && !missing.isEmpty then
        [s!"the clause at {tok p.at_} is about {reprStr missing}, which its judgements do not mention"] else []) ++
      ((aboutIssues c p here).map (s!"the clause at {tok p.at_} " ++ ·)) ++
      here.flatMap fun j =>
      match j.kind with
      | .event i =>
        match c.items[i]? with
        | none => [s!"no event {i} in the paragraph"]
        | some (e, _) =>
          (if p.neg && (e.content.map (·.2)) != some false then
            [s!"the clause at {tok p.at_} is negated, so it cannot assert the event {reprStr e}"] else [])
      | .claim cl =>
        (if cl.eval (c.stateAt (p.at_ + 1)) then [] else [s!"the claim at {tok p.at_} does not hold there"])
      | .content l =>
        let near : List Nat := p.parent.toList ++
          (f.preds.filter (·.parent == some p.at_)).map (·.at_) ++
          (f.links.filter (·.a == p.at_)).map (·.b) ++ (f.links.filter (·.b == p.at_)).map (·.a)
        let ok := near.any fun q => (judgesAt js q).any fun pj => match pj.kind with
          | .event i => ((c.items[i]?).bind (·.1.content)) == some l
          | .claim cl => cl.content == some l
          -- coordinated with content of the same thought ("hide behind the man and wait")
          | .content l' => l' == l && q != p.at_
          | _ => false
        if ok then [] else
        [s!"the clause at {tok p.at_} is read as content, but no clause it depends on (or that depends " ++
          "on it) is judged by a belief or speech with that literal"]
      | .goal l =>
        let gov := f.links.find? fun k => k.rel == .purpose && k.a == p.at_
        match gov with
        | none => [s!"the clause at {tok p.at_} is read as a goal, but it is not a purpose clause"]
        | some k =>
          let ok := (judgesAt js k.b).any fun gj => match gj.kind with
            | .event i => match (c.items[i]?).bind (·.1.agent) with
              | some ag => (goalsOf (run s.start (c.upToItem i).1) (⟨ag⟩ : Ch s)).contains (lit l)
              | none => false
            | _ => false
          if ok then [] else
          [s!"the purpose at {tok p.at_}: the one acting at {tok k.b} does not want that then"]
      | .act =>
        match p.subj with
        | some (.ch ch) =>
          let w := c.stateAt p.at_
          if (w.loc ⟨ch⟩).i < s.places.length then [] else [s!"the clause at {tok p.at_}: its subject is not on stage"]
        | _ => [s!"the clause at {tok p.at_} is read as a gesture, but its subject is not a character"]
      | .speech =>
        if p.quoted || p.said then [] else
        [s!"the clause at {tok p.at_} is read as speech, but it is neither quoted nor said by a verb of saying"]
      | .hypothetical =>
        if p.modal then [] else
        [s!"the clause at {tok p.at_} is read as hypothetical, but nothing in it is modal or conditional"]
      | .external _ => []
  let perLink := f.links.flatMap fun l =>
    let ja := judgesAt js l.a
    let jb := judgesAt js l.b
    if (ja ++ jb).any Judge.reported && l.rel != .condition then [] else
    let pos (xs : List Judge) : Option Nat := (xs.map (Judge.pos c)).max?
    let say (why : String) := [s!"'{l.word}' at {tok l.at_}: {why}"]
    match l.rel with
    | .after => match pos ja, pos jb with
      | some a, some b => if a ≤ b then [] else say "the second comes before the first in the story"
      | _, _ => []
    | .before => match pos ja, pos jb with
      | some a, some b => if b ≤ a then [] else say "it does not come before"
      | _, _ => []
    | .during => match pos ja, pos jb with
      | some a, some b => if a + 2 ≥ b && b + 2 ≥ a then [] else say "the two are not at the same time"
      | _, _ => []
    | .cause | .effect =>
      if ja.any fun a => jb.any fun b => causes c a b then [] else
      say "the model does not bear it out: with the cause taken out, the effect still holds (or the reason is not believed)"
    | .purpose =>
      if ja.any fun j => match j.kind with | .goal _ => true | _ => false then [] else
      say "the purpose clause must be read as a goal"
    | .concession =>
      if (ja ++ jb).all (ParaCtx.holds c) then [] else say "both sides must hold"
    | .condition =>
      if ja.any fun j => j.kind == .hypothetical then [] else say "the conditional clause must be read as hypothetical"
  let perMod := f.mods.flatMap fun m =>
    match m.of with
    | some ch =>
      if isTrait ch m.word then [] else
      if m.sense == some "impression" then [] else
      [s!"{tok m.at_} is said of {(s.chars[ch]?.map (·.name)).getD "?"}, who is not declared so: " ++
        "make it a trait, or mark the word \"sense\": \"impression\""]
    | none =>
      match m.sense with
      | some x => if modSenses.contains x then [] else [s!"{tok m.at_} has sense '{x}', not one of {", ".intercalate modSenses}"]
      | none => [s!"the adverb {tok m.at_} needs a sense ({", ".intercalate modSenses}), or is not one the model reads"]
  stray ++ perPred ++ perLink ++ perMod

def completeOk (c : ParaCtx s) (f : TreeFacts) (js : List Judge) : Bool :=
  (completeIssues c f js []).isEmpty

end LangLib.Studio

/-! ## Reading judgements from a paragraph's events file

```
"events": [{"e": "move ran lab", "at": 12, ...}]          each event is a judgement at its token
"claims": [{"c": "thinks hisoka gfUp", "at": 40, "w": "believed"}]
"judge":  [{"at": 7, "w": "smiled", "kind": "act"},
           {"at": 30, "w": "up", "kind": "content", "lit": "gfUp"},
           {"at": 44, "w": "hide", "kind": "goal", "lit": "chrolloHidden"},
           {"at": 20, "w": "drove", "kind": "external", "e": "use chrollo blackVoice judge left"}]
```
-/

namespace LangLib.Studio
open Lean LangLib LangLib.World

/-- World ids named in a move written in another file's words. -/
def Names.wids (n : Names) (str : String) : List WId :=
  let ws := ((str.splitOn " ").flatMap (·.splitOn "(")).flatMap (·.splitOn ",") |>.map
    (fun w => ((w.replace ")" "").replace "!" ""))
  ws.filterMap fun w =>
    (n.chars.idxOf? w).map WId.ch <|> (n.places.idxOf? w).map WId.pl <|> (n.objects.idxOf? w).map WId.ob

private def jarr (j : Json) (k : String) : List Json :=
  match j.getObjVal? k with | .ok (.arr a) => a.toList | _ => []

/-- The judgements of a paragraph's events file. -/
def judgesOf (s : Spec) (j : Json) : Except String (List Judge) := do
  let n := s.names
  let evs := (jarr j "events").zipIdx.filterMap fun (e, i) =>
    (e.getObjValAs? Nat "at").toOption.map fun a => ({ at_ := a, kind := .event i } : Judge)
  let claims ← (jarr j "claims").filterMapM fun c => do
    match (c.getObjValAs? String "c").toOption, (c.getObjValAs? Nat "at").toOption with
    | some str, some a => pure (some ({ at_ := a, kind := .claim (← n.claim str) } : Judge))
    | _, _ => pure none
  let other ← (jarr j "judge").mapM fun x => do
    let some a := (x.getObjValAs? Nat "at").toOption | throw "a judgement needs \"at\""
    let kind := (x.getObjValAs? String "kind").toOption.getD ""
    let litOf : Except String (Fact × Bool) := match (x.getObjValAs? String "lit").toOption with
      | some l => n.lit l
      | none => throw s!"a {kind} judgement needs \"lit\""
    let k : JKind ← match kind with
      | "content" => pure (.content (← litOf))
      | "goal" => pure (.goal (← litOf))
      | "act" => pure .act
      | "speech" => pure .speech
      | "hypothetical" => pure .hypothetical
      | "external" => pure (.external (n.wids ((x.getObjValAs? String "e").toOption.getD "")))
      | _ => throw s!"unknown judgement kind \"{kind}\" (content, goal, act, speech, hypothetical, external)"
    pure ({ at_ := a, kind := k } : Judge)
  pure (evs ++ claims ++ other)

/-- Claims written without an anchor (not allowed in a complete story). -/
def unanchoredClaims (j : Json) : List String :=
  (jarr j "claims").filterMap fun c => c.getStr?.toOption

def judgesMatch (s : Spec) (str : String) (js : List Judge) : Bool :=
  match Json.parse str >>= judgesOf s with
  | .ok js' => js' == js
  | .error _ => false

def treeMatch (s : Spec) (str : String) (f : TreeFacts) : Bool :=
  match docOfString str with
  | .ok d => treeFacts s d == f
  | .error _ => false

end LangLib.Studio

/-! ## Derivations: why each verdict holds, as inference rules

`derivations` restates the checks of `completeIssues` as proof trees: each
clause, connective and modifier is a conclusion over the premises that
justify it, under a named rule (EVENT, HOLDS, CONTENT, GOAL, AGREE, LORE,
BUT-FOR, REASON, ORDER, ...). It uses the same predicates, so a premise marked
failed is exactly what the checker objects to. The Studio draws them as
Gentzen-style trees. -/

namespace LangLib.Studio
open Lean LangLib LangLib.World LangLib.Scene

inductive Deriv where
  | mk (rule concl : String) (ok : Bool) (prems : List Deriv)
  deriving Repr, Inhabited

partial def Deriv.toJson : Deriv → Json
  | .mk rule concl ok prems => Json.mkObj [("rule", rule), ("concl", concl), ("ok", ok),
      ("prems", Json.arr (prems.map Deriv.toJson).toArray)]

def Deriv.ok : Deriv → Bool | .mk _ _ ok _ => ok

def Names.claimS (n : Names) : Claim → String
  | .thinks c l => s!"thinks {n.chS c} {n.litS l}"
  | .knows c l => s!"knows {n.chS c} {n.litS l}"
  | .falseBelief c l => s!"falseBelief {n.chS c} {n.litS l}"
  | .unaware c f => s!"unaware {n.chS c} {n.factS f}"
  | .thinksThinks c d l => s!"thinksThinks {n.chS c} {n.chS d} {n.litS l}"
  | .holdsTrue l => s!"true {n.litS l}"
  | .consented b a x => s!"consented {n.chS b} {n.chS a} {x.name}"
  | .goal c l => s!"goal {n.chS c} {n.litS l}"
  | .bond a b d _ v => s!"bond {n.chS a} {n.chS b} {d.name} {v}"

variable {s : Spec}

def WId.show (n : Names) : WId → String
  | .ch i => n.chS i | .pl i => n.plS i | .ob i => n.obS i

private def leaf (rule concl : String) (ok : Bool) : Deriv := .mk rule concl ok []

/-! ### Evidence -/

/-- A story event back in the surface syntax. -/
def E.toEv : E s → Ev
  | .action a => A.toEv a
  | .goal (.adopt c g) => .adopt c.i (unlit g)
  | .goal (.drop c g) => .dropGoal c.i (unlit g)
  | .goal (.intend c _) => .intend c.i 0
  | .goal (.abandon c g) => .abandon c.i (unlit g)

/-- The last event of `es` after which `p` changed, if any. -/
def lastTurn (es : List (E s)) (p : W s → Bool) : Option Nat := Id.run do
  let mut w := s.start
  let mut at_ : Option Nat := none
  for (e, i) in es.zipIdx do
    let w' := next w e
    if p w != p w' then at_ := some i
    w := w'
  return at_

/-- Where event `i` of a paragraph's story-so-far is: this paragraph's word, or earlier. -/
def ParaCtx.where_ (c : ParaCtx s) (toks : List String) (es : List (E s)) (i : Nat) : String :=
  let gloss := ((es[i]?).map fun e => s.evGloss (E.toEv e)).getD "?"
  if i < c.prior.length then s!"{gloss} (earlier in the story)"
  else match c.items[i - c.prior.length]? with
    | some (_, t) => s!"{gloss} (at ‘{toks.getD t "?"}’)"
    | none => gloss

/-- Why a fact holds (or not) at the end of `es`: the event that last turned it. -/
def provenance (c : ParaCtx s) (toks : List String) (es : List (E s)) (l : Fact × Bool) : String :=
  let p := fun (w : W s) => truthLit w (lit (s := s) l)
  match lastTurn es p with
  | some i => s!"made so by: {c.where_ toks es i}"
  | none => if p s.start then "so from the start (the world as story.json sets it)" else "never so"

def evidSay (s : Spec) : Evid Nat → String
  | .told d => s!"told by {s.charName d}" | .relayed d => s!"heard second-hand from {s.charName d}"
  | .seen => "seen" | .sensed => "sensed" | .inferred => "their own inference"
  | .assumed => "assumed" | .rumour => "rumour" | .self => "they know it themselves"

/-- What `ch` holds about `l` in `w`, and on what evidence. -/
def beliefEvidence (w : W s) (ch : Nat) (l : Fact × Bool) : List String :=
  let v := view w (⟨ch⟩ : Ch s)
  (HasMinds.beliefs w (⟨ch⟩ : Ch s)).filterMap fun h =>
    match litOf h.b with
    | some l' =>
      if l'.1.f != l.1 then none else
      let what := (if l'.2 then "" else "not: ") ++ s.factGloss l'.1.f
      let st := if h.up == .note then "only noted" else if v.contains l' then "believed" else "outranked"
      some s!"{evidSay s (Evid.ofCh h.src)}: {what} ({st})"
    | none => none

def claimGloss (s : Spec) (cl : Claim) : String :=
  match cl with
  | .thinks c l => s!"{s.charName c} believes: {s.litGloss l}"
  | .knows c l => s!"{s.charName c} knows: {s.litGloss l}"
  | .falseBelief c l => s!"{s.charName c} wrongly believes: {s.litGloss l}"
  | .unaware c f => s!"{s.charName c} has no view on: {s.factGloss f}"
  | .thinksThinks c d l => s!"{s.charName c} thinks {s.charName d} believes: {s.litGloss l}"
  | .holdsTrue l => s.litGloss l
  | .consented b a x => s!"{s.charName b} consents to {x.name} with {s.charName a}"
  | .goal c l => s!"{s.charName c} wants: {s.litGloss l}"
  | .bond a b d _ v => s!"{s.charName a}'s {d.name} toward {s.charName b} is {v}"

/-- The story with its events in order up to the paragraph's end. -/
def ParaCtx.whole (c : ParaCtx s) : List (E s) := c.prior ++ c.items.map fun (x : Ev × Nat) => Ev.toE s x.1

/-! ### Judgements and their derivations -/

/-- How a judgement is justified, with its evidence. -/
def judgeDeriv (c : ParaCtx s) (f : TreeFacts) (js : List Judge) (toks : List String)
    (p : Pred) (j : Judge) : Deriv :=
  let n := s.names
  let w (t : Nat) := s!"‘{toks.getD t "?"}’"
  match j.kind with
  | .event i =>
    match c.items[i]? with
    | none => leaf "event" s!"event {i}" false
    | some (e, _) =>
      let (es, k) := c.upToItem i
      let before := run s.start (es.take k)
      let allowed := okAt s.start es k
      let negOk := !p.neg || (e.content.map (·.2)) == some false
      let motive : List Deriv :=
        match ((motives (C := Ch s) (Φ := SFact s) (E := A s) s.start es 0).find? (·.1 == k)).map (·.2) with
        | some (Motive.goal ag g) => [leaf "motive" s!"done because {s.charName ag.i} wants: {s.litGloss (unlit g)}" true]
        | some (Motive.step ag g) => [leaf "motive" s!"a step of {s.charName ag.i}'s plan for: {s.litGloss (unlit g)}" true]
        | some (Motive.none ag) => [leaf "motive" s!"{s.charName ag.i} has no reason for it" false]
        | none => []
      let pre : List Deriv := match e with
        | .tell sp _ l | .whisper sp _ l =>
          [leaf "sincere" s!"{s.charName sp} believes it: {s.litGloss l}" ((view before (⟨sp⟩ : Ch s)).contains (lit l))]
        | .lie sp _ l =>
          [leaf "a lie" s!"{s.charName sp} does not believe it: {s.litGloss l}" (!(view before (⟨sp⟩ : Ch s)).contains (lit l))]
        | .notice _ l ev =>
          if ev == .seen || ev == .sensed then
            [leaf "perceived" s!"it is so: {s.litGloss l}; {provenance c toks (es.take k) l}" (truthLit before (lit (s := s) l))]
          else [leaf "concluded" s!"their own conclusion ({evidSay s ev})" true]
        | _ => []
      .mk "event" (s.evGloss e) (allowed && negOk)
        (pre ++ motive ++ (if allowed then [] else [leaf "not allowed" (Domain.why before (Ev.toE s e)) false]) ++
         (if p.neg then [leaf "negated" "a negated clause asserts no event, unless its literal is negative" negOk] else []))
  | .claim cl =>
    let st := c.stateAt (p.at_ + 1)
    let ok := cl.eval st
    let es := c.upToTok (p.at_ + 1)
    let evidence : List Deriv := match cl with
      | .holdsTrue l => [leaf "the world" (provenance c toks es l) ok]
      | .thinks ch l | .knows ch l | .falseBelief ch l =>
        (beliefEvidence st ch l).map (leaf "evidence" · true) ++
        (match cl with
         | .knows _ l => [leaf "the world" (provenance c toks es l) (truthLit st (lit (s := s) l))]
         | .falseBelief _ l => [leaf "the world" s!"in fact not so: {provenance c toks es (l.1, !l.2)}" (!truthLit st (lit (s := s) l))]
         | _ => [])
      | _ => []
    .mk "claim" (claimGloss s cl) ok (if evidence.isEmpty then [leaf "holds" s!"at {w p.at_}" ok] else evidence)
  | .content l =>
    let near : List Nat := p.parent.toList ++
      (f.preds.filter (·.parent == some p.at_)).map (·.at_) ++
      (f.links.filter (·.a == p.at_)).map (·.b) ++ (f.links.filter (·.b == p.at_)).map (·.a)
    let src := near.findSome? fun q => (judgesAt js q).findSome? fun pj => match pj.kind with
      | .event i => ((c.items[i]?).bind fun (e, _) => if e.content == some l then some s!"{w q}: {s.evGloss e}" else none)
      | .claim cl => if cl.content == some l then some s!"{w q}: {claimGloss s cl}" else none
      | .content l' => if l' == l && q != p.at_ then some s!"{w q}: the same thought" else none
      | _ => none
    .mk "content" s!"what is believed or said: {s.litGloss l}" src.isSome
      [leaf "of" (src.getD "no clause nearby believes or says it") src.isSome]
  | .goal l =>
    let gov := f.links.find? fun k => k.rel == .purpose && k.a == p.at_
    match gov with
    | none => .mk "goal" s!"a purpose: {s.litGloss l}" false [leaf "purpose" "not a purpose clause" false]
    | some k =>
      let agentOk := (judgesAt js k.b).findSome? fun gj => match gj.kind with
        | .event i => (c.items[i]?).bind fun (e, _) => e.agent.map fun ag =>
            (s.charName ag, (goalsOf (run s.start (c.upToItem i).1) (⟨ag⟩ : Ch s)).contains (lit l))
        | _ => none
      match agentOk with
      | some (ag, ok) => .mk "goal" s!"{ag}'s purpose: {s.litGloss l}" ok
          [leaf "wants" s!"{ag} wants it when acting at {w k.b}" ok]
      | none => .mk "goal" s!"a purpose: {s.litGloss l}" false [leaf "wants" s!"no one acts at {w k.b}" false]
  | .act =>
    match p.subj with
    | some (.ch ch) =>
      let ok := ((c.stateAt p.at_).loc ⟨ch⟩).i < s.places.length
      .mk "gesture" s!"something {s.charName ch} does, with no other world content" ok
        [leaf "on stage" s!"{s.charName ch} is in the {s.places.getD ((c.stateAt p.at_).loc ⟨ch⟩).i "?"}" ok]
    | _ => .mk "gesture" "a gesture" false [leaf "on stage" "its subject is not a character" false]
  | .speech =>
    let ok := p.quoted || p.said
    .mk "speech" "words said, not a claim about the world" ok
      [leaf (if p.quoted then "quoted" else "said") (if p.quoted then "inside a quote" else s!"what ‘{p.parentLemma}’ says") ok]
  | .hypothetical =>
    .mk "hypothetical" "not asserted" p.modal [leaf "modal" "under a modal or a condition" p.modal]
  | .external ids =>
    .mk "Nen move" s!"a move about {", ".intercalate (ids.map (WId.show n))}" true
      [leaf "proved" "checked move by move in LangLib/World/Examples/Fight.lean" true]

/-- A clause's judgement: Γ¶ ⊢ «its words» ⟹ what they mean, by each of its judgements. -/
def clauseDeriv (c : ParaCtx s) (f : TreeFacts) (js : List Judge) (toks : List String) (p : Pred) : Deriv :=
  let n := s.names
  let here := judgesAt js p.at_
  let refs := p.subj.toList ++ p.args
  let ids : List WId := here.flatMap fun j => match j.kind with
    | .event i => ((c.items[i]?).map (Ev.wids s ·.1)).getD []
    | .claim cl => Claim.wids s cl
    | .external xs => xs
    | _ => []
  let worldJudged := here.any fun j => match j.kind with
    | .event _ | .claim _ | .external _ => true | _ => false
  let missing := refs.filter (!ids.contains ·)
  let agree := if !worldJudged || refs.isEmpty then [] else
    [leaf "mentions" (if missing.isEmpty then s!"about {", ".intercalate (refs.map (WId.show n))}, as its words are"
      else s!"its words are about {", ".intercalate (missing.map (WId.show n))}, which its judgements are not") missing.isEmpty]
  let aboutIs := aboutIssues c p here
  let about := if (p.thing.isNone && p.kinds.isEmpty) || here.isEmpty || here.all Judge.reported then [] else
    [leaf "about" (if aboutIs.isEmpty then "judged by facts about what its words name" else " ".intercalate aboutIs)
      aboutIs.isEmpty]
  let prems := here.map (judgeDeriv c f js toks p) ++ agree ++ about
  .mk "clause" s!"«{p.text}»" (!here.isEmpty && prems.all (·.ok))
    (if here.isEmpty then [leaf "unjudged" "nothing in the world says what these words assert" false] else prems)

/-- Why a connective holds (or not). -/
def linkDeriv (c : ParaCtx s) (js : List Judge) (toks : List String) (l : Link) : Deriv :=
  let n := s.names
  let w (t : Nat) := s!"‘{toks.getD t "?"}’"
  let ja := judgesAt js l.a
  let jb := judgesAt js l.b
  let concl := s!"‘{l.word}’: {w l.a} {match l.rel with
    | .cause | .effect => "causes" | .purpose => "is the purpose of" | .after => "comes before"
    | .before => "comes after" | .during => "is at the same time as" | .concession => "holds, and so does"
    | .condition => "is supposed for"} {w l.b}"
  if (ja ++ jb).any Judge.reported && l.rel != .condition then
    .mk "reported" concl true [leaf "inside a report" "said or thought by a character: their claim, not the world's" true]
  else
  let pos (xs : List Judge) : Option Nat := (xs.map (Judge.pos c)).max?
  match l.rel with
  | .after | .before | .during =>
    match pos ja, pos jb with
    | some a, some b =>
      let ok := match l.rel with
        | .after => a ≤ b | .before => b ≤ a | _ => a + 2 ≥ b && b + 2 ≥ a
      .mk "time" concl ok [leaf "order" s!"{w l.a} is at step {a / 2} of the paragraph, {w l.b} at step {b / 2}" ok]
    | _, _ => .mk "time" concl true []
  | .cause | .effect =>
    let ways : List Deriv := ja.flatMap fun a => jb.filterMap fun b =>
      if !causes c a b then none else
      match a.kind, b.kind with
      | .claim ca, .claim cb =>
        match ca.content, cb.content with
        | some la, some lb => some (.mk "lore" concl true
            [leaf "fact" (claimGloss s ca) true, leaf "rule" s!"whenever {s.litGloss la}, {s.litGloss lb}" true,
             leaf "fact" (claimGloss s cb) true])
        | _, _ => none
      | .event i, .event k =>
        let (es, jj) := c.upToItem k
        let es' := es.eraseIdx (c.prior.length + i)
        let w' := run s.start (es'.take (jj - 1))
        let why := match es'[jj - 1]? with
          | some e => if Domain.ok w' e then "it would have no reason" else Domain.why w' e
          | none => "?"
        some (.mk "but for" concl true
          [leaf "without it" s!"take {w l.a}'s event out of the story, and {w l.b}'s cannot happen: {why}" true])
      | .event _, _ => some (.mk "but for" concl true
          [leaf "without it" s!"take {w l.a}'s event out of the story, and what {w l.b} says no longer holds" true])
      | _, .event k =>
        let ag := ((c.items[k]?).bind (·.1.agent)).map s.charName
        some (.mk "reason" concl true
          [leaf "believed" s!"{ag.getD "the one acting"} believed what {w l.a} says when acting at {w l.b}" true])
      | _, _ => none
    match ways.head? with
    | some d => d
    | none => .mk "cause" concl false [leaf "not borne out" "no lore rule, counterfactual or belief connects them" false]
  | .purpose =>
    let ok := ja.any fun j => match j.kind with | .goal _ => true | _ => false
    .mk "purpose" concl ok [leaf "goal" s!"{w l.a} is read as the goal of {w l.b}" ok]
  | .concession =>
    let ok := (ja ++ jb).all (ParaCtx.holds c)
    .mk "both hold" concl ok [leaf "holds" s!"{w l.a} holds" ok, leaf "holds" s!"{w l.b} holds" ok]
  | .condition =>
    let ok := ja.any fun j => j.kind == .hypothetical
    .mk "supposition" concl ok [leaf "hypothetical" s!"{w l.a} is read as hypothetical" ok]

def modDeriv (sp : Spec) (toks : List String) (m : Modifier) : Deriv :=
  let isTrait := match m.of, Trait.ofString? m.word with
    | some ch, some t => (sp.chars[ch]?.map fun (cs : CharSpec) => cs.traits.contains t).getD false
    | _, _ => false
  let concl := s!"‘{toks.getD m.at_ m.word}’"
  match m.of with
  | some ch =>
    let who := (sp.chars[ch]?.map CharSpec.name).getD "?"
    if isTrait then .mk "trait" concl true [leaf "persona" s!"{who} is {m.word} (story.json)" true]
    else .mk "impression" concl (m.sense == some "impression")
      [leaf "sense" (if m.sense == some "impression" then s!"how {who} seems, not a fact about them"
        else s!"said of {who}, who is not declared so, and not marked an impression") (m.sense == some "impression")]
  | none =>
    let ok := (m.sense.map modSenses.contains).getD false
    .mk "sense" concl ok [leaf "sense" (match m.sense with | some x => s!"a word of {x}" | none => "no sense given") ok]

/-- Every derivation of a paragraph, in token order. -/
def derivations (c : ParaCtx s) (f : TreeFacts) (js : List Judge) (toks : List String) : List (Nat × Deriv) :=
  ((f.preds.map fun p => (p.at_, clauseDeriv c f js toks p)) ++
   (f.links.filter (fun l => l.a != l.b)).map (fun l => (l.at_, linkDeriv c js toks l)) ++
   f.mods.map fun m => (m.at_, modDeriv s toks m)).mergeSort (fun a b => a.1 ≤ b.1)

end LangLib.Studio

/-! ## The story as an argument graph

Nodes are the facts the story asserts (claims that something is true, what is
seen), the beliefs it gives its characters (belief claims, what they are told
or notice) and what is said. Support edges: told (a saying supports the
hearer's belief), seen (a fact supports the seer's belief), a connective
("because", "so") between the clauses' facts or beliefs, a lore rule between
facts. Attack edges (Dung): the fact that contradicts a false belief attacks
it, and a later belief revises (attacks) an earlier one it contradicts. Facts
are unattacked, so the grounded labelling is: facts in, what they attack out,
the rest in. -/

namespace LangLib.Studio
open Lean LangLib LangLib.World

structure ANode where
  id : String
  kind : String          -- fact | belief | said
  who : String := ""     -- the believer or speaker
  lit : String
  gloss : String
  para : String
  status : String := "in"
  note : String := ""
  /-- where the story asserts it: (paragraph, token) -/
  ats : List (String × Nat) := []
  deriving Inhabited

structure AEdge where
  src : String
  tgt : String
  kind : String          -- support | attack
  why : String
  deriving Inhabited

/-- One paragraph's material: its name, context, tree facts, judgements and tokens. -/
abbrev ParaData (s : Spec) := String × ParaCtx s × TreeFacts × List Judge × List String

def argumentGraph (s : Spec) (ps : List (ParaData s)) : List ANode × List AEdge := Id.run do
  let n := s.names
  let mut nodes : Array ANode := #[]
  let mut edges : Array AEdge := #[]
  let flip (l : Fact × Bool) : Fact × Bool := (l.1, !l.2)
  let factId (l : Fact × Bool) := s!"F:{n.litS l}"
  let belId (c : Nat) (l : Fact × Bool) := s!"B:{n.chS c}:{n.litS l}"
  let fact (l : Fact × Bool) (para status note : String) : ANode :=
    ANode.mk (factId l) "fact" "" (n.litS l) (s.litGloss l) para status note []
  let belief (c : Nat) (l : Fact × Bool) (para status : String) : ANode :=
    ANode.mk (belId c l) "belief" (n.chS c) (n.litS l) (s.litGloss l) para status "" []
  let add (nodes : Array ANode) (x : ANode) : Array ANode :=
    if nodes.any (·.id == x.id) then nodes else nodes.push x
  for (name, c, f, js, toks) in ps do
    let w (t : Nat) := s!"‘{toks.getD t "?"}’"
    -- truth where the judgement stands: after its event in story order, or at its token
    let inOut (j : Judge) (l : Fact × Bool) : String :=
      let st := match j.kind with
        | .event i => run s.start (c.upToItem i).1
        -- a claim's fact: true or false by the end of its paragraph, in story order (prose may
        -- tell a move after the belief it explains)
        | _ => run s.start (c.prior ++ c.items.map fun (x : Ev × Nat) => Ev.toE s x.1)
      if truthLit st (lit (s := s) l) then "in" else "out"
    -- the node a judgement stands for, if any
    let nodeOf (j : Judge) : Option ANode :=
      match j.kind with
      | .claim (.holdsTrue l) => some (fact l name (inOut j l) "")
      | .claim (.thinks ch l) | .claim (.knows ch l) | .claim (.falseBelief ch l) =>
        some (belief ch l name (inOut j l))
      | .event i => (c.items[i]?).bind fun (e, _) => match e with
        | .tell _ d l | .whisper _ d l | .lie _ d l => some (belief d l name (inOut j l))
        | .notice ch l _ | .realise ch l => some (belief ch l name (inOut j l))
        | _ => none
      | _ => none
    for j in js do
      -- a node seen again takes its status there: a belief true when formed can turn false
      if let some x := nodeOf j then
        let here := (name, j.at_)
        nodes := match nodes.findIdx? (·.id == x.id) with
          | some k =>
            let old := nodes[k]!
            let ats := if old.ats.contains here then old.ats else old.ats ++ [here]
            if old.status == x.status then nodes.set! k { old with ats } else
            let note := s!"{if x.status == "out" then "false" else "true"} from ¶ {name}"
            nodes.set! k { old with status := x.status, note, ats }
          | none => nodes.push { x with ats := [here] }
      -- what supports a belief: being told, seeing
      if let .event i := j.kind then
        if let some (e, _) := c.items[i]? then
          match e with
          | .tell sp d l | .whisper sp d l | .lie sp d l =>
            let note := match e with | .lie .. => "a lie" | _ => ""
            let said := ANode.mk s!"S:{n.chS sp}:{n.litS l}" "said" (n.chS sp) (n.litS l) (s.litGloss l) name "in" note
              [(name, j.at_)]
            nodes := add nodes said
            edges := edges.push ⟨said.id, belId d l, "support", "told"⟩
          | .notice ch l ev =>
            if (ev == .seen || ev == .sensed) && inOut j l == "in" then
              nodes := add nodes (fact l name "in" "")
              edges := edges.push ⟨factId l, belId ch l, "support", "seen"⟩
          | _ => pure ()
    -- connectives the model bears out: support between the clauses' nodes
    for l in f.links do
      if l.rel == .cause || l.rel == .effect then
        for a in judgesAt js l.a do
          for b in judgesAt js l.b do
            match nodeOf a, nodeOf b with
            | some na, some nb =>
              if causes c a b then
                edges := edges.push ⟨na.id, nb.id, "support", s!"‘{l.word}’ ({w l.a} → {w l.b})"⟩
            | _, _ => pure ()
  -- lore rules between facts in the graph
  for r in Lore.rules (Φ := SFact s) do
    let hd : Fact × Bool := (r.head.1.f, r.head.2)
    for b in r.body do
      let bd : Fact × Bool := (b.1.f, b.2)
      if nodes.any (·.id == factId bd) && nodes.any (·.id == factId hd) then
        edges := edges.push ⟨factId bd, factId hd, "support", "lore"⟩
  -- attacks: the world against false beliefs, later beliefs against earlier ones
  let order (p : String) : Nat := ((ps.map (·.1)).idxOf? p).getD 0
  for x in nodes do
    if x.kind == "belief" && x.status == "out" then
      if let .ok l := n.lit x.lit then
        nodes := add nodes (fact (flip l) x.para "in" "the world")
        edges := edges.push ⟨factId (flip l), x.id, "attack", "the world says otherwise"⟩
  for x in nodes do
    for y in nodes do
      if x.kind == "belief" && y.kind == "belief" && x.who == y.who && order y.para > order x.para then
        if let (.ok lx, .ok ly) := (n.lit x.lit, n.lit y.lit) then
          if lx.1 == ly.1 && lx.2 != ly.2 then
            edges := edges.push ⟨y.id, x.id, "attack", s!"revised in ¶ {y.para}"⟩
  return (nodes.toList, edges.toList)

def argumentJson (g : List ANode × List AEdge) : Json :=
  Json.mkObj [
    ("nodes", Json.arr (g.1.map fun x => Json.mkObj [("id", x.id), ("kind", x.kind), ("who", x.who), ("lit", x.lit),
      ("gloss", x.gloss), ("para", x.para), ("status", x.status), ("note", x.note),
      ("ats", Json.arr (x.ats.map fun (p, t) => Json.str s!"tok:{p}:{t}").toArray)]).toArray),
    ("edges", Json.arr (g.2.map fun e => Json.mkObj [("src", e.src), ("tgt", e.tgt), ("kind", e.kind),
      ("why", e.why)]).toArray)]

end LangLib.Studio

/-! ## Where each clause is in the text

For drawing: each clause (by its head token) with the tokens of its own words,
subject first, the clauses inside it left out (as `Pred.text`). Report only;
the proofs do not depend on it. -/

namespace LangLib.Studio
open LangLib

private def isClauseNode (t : Tree) : Bool := match t with
  | .node ki _ => ki.cat == .S || ki.cat == .SBAR || (ki.role.map clauseRoles.contains).getD false
  | .leaf _ => false

/-- Token positions of a node's own words (as `ownWords`). -/
partial def ownIdx : Tree → Nat → List Nat
  | .leaf w, p => if w.upos == .PUNCT then [] else [p]
  | .node _ kids, start =>
    let offs := (kids.foldl (fun (acc, p) k => (acc ++ [p], p + k.render.length)) (([] : List Nat), start)).1
    (kids.zip offs).flatMap fun (k, o) => if isClauseNode k then [] else ownIdx k o

/-- (head token, tokens) for every clause of a tree. -/
partial def spansIn (subjIdx : List Nat) : Tree → Nat → List (Nat × List Nat)
  | .leaf _, _ => []
  | t@(.node _ kids), start =>
    let offs := (kids.foldl (fun (acc, p) k => (acc ++ [p], p + k.render.length)) (([] : List Nat), start)).1
    let placed := kids.zip offs
    let isHead (k : Tree) := match k with | .leaf w => w.role == some .head | .node i _ => i.role == some .head
    let verb := placed.findSome? fun (k, o) => match k with
      | .leaf w => if w.upos == .VERB && w.role == some .head then some o else none
      | _ => none
    let cop := placed.findSome? fun (k, o) => match k with
      | .leaf w => if w.role == some .cop then some o else none
      | .node i _ => if i.role == some .cop then some o else none
    let at_ : Option Nat := match verb, cop with
      | some o, _ => some o
      | none, some c => some (((placed.find? fun (k, _) => isHead k).map (·.2)).getD c)
      | none, none => none
    let nsubj := placed.find? fun (k, _) => match k with
      | .leaf w => w.role == some .nsubj | .node i _ => i.role == some .nsubj
    let subjIdx := match nsubj with | some (k, o) => ownIdx k o | none => subjIdx
    let here := match at_ with
      | some a =>
        let own := ownIdx t start
        [(a, ((if nsubj.isSome then [] else subjIdx) ++ own).eraseDups.mergeSort (· ≤ ·))]
      | none => []
    here ++ placed.flatMap fun (k, o) => spansIn subjIdx k o

def clauseSpans (d : Doc) : List (Nat × List Nat) :=
  (d.sentences.foldl (fun (acc, p) sn => (acc ++ spansIn [] sn.tree p, p + sn.tree.render.length))
    (([] : List (Nat × List Nat)), 0)).1

end LangLib.Studio
