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
  `World/Cause.lean`); "to", "in order to", "so that" (purpose: the clause is
  judged `goal`); "though", "although" (both hold); "if", "as if", "unless",
  "whether" (the dependent clause is hypothetical).
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
    let me := me.map fun p =>
      let near := kids.flatMap shallowLeaves
      { p with
        args := (kids.filter fun k => roleIs k .obj || roleIs k .iobj || roleIs k .obl).filterMap
          (fun k => (refOf k).bind (wid s R)),
        neg := near.any fun w => negWords.contains (lower w),
        modal := ctx.cond || near.any fun w => w.upos == .AUX && modalWords.contains (lower w),
        quoted, said := ctx.said, parent := ctx.parent, parentLemma := ctx.parentLemma }
    let ctx' : TCtx := match me with
      | some p => { subj, parent := some p.at_, parentLemma := p.lemma, quoted, cond := p.modal,
                    said := ctx.said || speechVerbs.contains p.lemma }
      | none => { ctx with subj, quoted }
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
          match LinkRel.ofMarker phrase, marks.head?, headAt k o, hereAt with
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

/-- How a judgement is justified. -/
def judgeDeriv (c : ParaCtx s) (f : TreeFacts) (js : List Judge) (toks : List String)
    (p : Pred) (j : Judge) : Deriv :=
  let n := s.names
  let w (t : Nat) := s!"‘{toks.getD t "?"}’"
  match j.kind with
  | .event i =>
    match c.items[i]? with
    | none => leaf "EVENT" s!"event {i}" false
    | some (e, _) =>
      let (es, k) := c.upToItem i
      let allowed := okAt s.start es k
      let negOk := !p.neg || (e.content.map (·.2)) == some false
      .mk "EVENT" (n.evS e) (allowed && negOk)
        ([leaf "VALID" s!"allowed where it stands: {s.evGloss e}" allowed] ++
         (if p.neg then [leaf "NEG" "the clause is negated, so the event's literal must be negative" negOk] else []))
  | .claim cl =>
    let ok := cl.eval (c.stateAt (p.at_ + 1))
    .mk "HOLDS" s!"⊨ {n.claimS cl}" ok [leaf "STATE" s!"in the state at {w p.at_}" true]
  | .content l =>
    let near : List Nat := p.parent.toList ++
      (f.preds.filter (·.parent == some p.at_)).map (·.at_) ++
      (f.links.filter (·.a == p.at_)).map (·.b) ++ (f.links.filter (·.b == p.at_)).map (·.a)
    let src := near.findSome? fun q => (judgesAt js q).findSome? fun pj => match pj.kind with
      | .event i => ((c.items[i]?).bind fun (e, _) => if e.content == some l then some s!"{w q}: {n.evS e}" else none)
      | .claim cl => if cl.content == some l then some s!"{w q}: {n.claimS cl}" else none
      | .content l' => if l' == l && q != p.at_ then some s!"{w q}: content {n.litS l'}" else none
      | _ => none
    .mk "CONTENT" s!"content: {n.litS l}" src.isSome
      [leaf "SOURCE" (src.getD "no clause nearby believes or says it") src.isSome]
  | .goal l =>
    let gov := f.links.find? fun k => k.rel == .purpose && k.a == p.at_
    match gov with
    | none => .mk "GOAL" s!"goal: {n.litS l}" false [leaf "PURPOSE" "not a purpose clause" false]
    | some k =>
      let agentOk := (judgesAt js k.b).findSome? fun gj => match gj.kind with
        | .event i => (c.items[i]?).bind fun (e, _) => e.agent.map fun ag =>
            (n.chS ag, (goalsOf (run s.start (c.upToItem i).1) (⟨ag⟩ : Ch s)).contains (lit l))
        | _ => none
      match agentOk with
      | some (ag, ok) => .mk "GOAL" s!"goal: {n.litS l}" ok
          [leaf "PURPOSE" s!"the purpose of {w k.b}" true, leaf "WANTS" s!"{ag} wants {n.litS l} then" ok]
      | none => .mk "GOAL" s!"goal: {n.litS l}" false [leaf "WANTS" s!"no one acts at {w k.b}" false]
  | .act =>
    match p.subj with
    | some (.ch ch) =>
      let ok := ((c.stateAt p.at_).loc ⟨ch⟩).i < s.places.length
      .mk "ACT" "a gesture" ok [leaf "ON-STAGE" s!"{n.chS ch} is on stage" ok]
    | _ => .mk "ACT" "a gesture" false [leaf "ON-STAGE" "the subject is not a character" false]
  | .speech =>
    let ok := p.quoted || p.said
    .mk "SPEECH" "words said" ok [leaf (if p.quoted then "QUOTED" else "SAID")
      (if p.quoted then "inside a quote" else s!"what ‘{p.parentLemma}’ says") ok]
  | .hypothetical =>
    .mk "HYPOTHETICAL" "not asserted" p.modal [leaf "MODAL" "under a modal or a condition" p.modal]
  | .external ids =>
    .mk "EXTERNAL" s!"a Nen move about {", ".intercalate (ids.map (WId.show n))}" true
      [leaf "CHECKED" "proved in Fight.lean" true]

/-- How a clause is judged: its judgements, and that they mention what it does. -/
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
    [leaf "AGREE" (if missing.isEmpty then s!"mentions {", ".intercalate (refs.map (WId.show n))}"
      else s!"does not mention {", ".intercalate (missing.map (WId.show n))}") missing.isEmpty]
  let prems := here.map (judgeDeriv c f js toks p) ++ agree
  .mk "CLAUSE" s!"‘{toks.getD p.at_ "?"}’ is judged" (!here.isEmpty && prems.all (·.ok))
    (if here.isEmpty then [leaf "NONE" "no judgement" false] else prems)

/-- Why a connective holds (or not). -/
def linkDeriv (c : ParaCtx s) (js : List Judge) (toks : List String) (l : Link) : Deriv :=
  let n := s.names
  let w (t : Nat) := s!"‘{toks.getD t "?"}’"
  let ja := judgesAt js l.a
  let jb := judgesAt js l.b
  let concl := s!"‘{l.word}’: {w l.a} → {w l.b}"
  if (ja ++ jb).any Judge.reported && l.rel != .condition then
    .mk "REPORTED" concl true [leaf "IN-CONTENT" "inside reported speech or thought: the speaker's claim, not the world's" true]
  else
  let pos (xs : List Judge) : Option Nat := (xs.map (Judge.pos c)).max?
  match l.rel with
  | .after | .before | .during =>
    match pos ja, pos jb with
    | some a, some b =>
      let ok := match l.rel with
        | .after => a ≤ b | .before => b ≤ a | _ => a + 2 ≥ b && b + 2 ≥ a
      .mk "ORDER" concl ok [leaf "AT" s!"{w l.a} at step {a / 2}" true, leaf "AT" s!"{w l.b} at step {b / 2}" true]
    | _, _ => .mk "ORDER" concl true []
  | .cause | .effect =>
    -- the first way the model bears it out, if any
    let ways : List Deriv := ja.flatMap fun a => jb.filterMap fun b =>
      if !causes c a b then none else
      match a.kind, b.kind with
      | .claim ca, .claim cb =>
        match ca.content, cb.content with
        | some la, some lb => some (.mk "LORE" concl true
            [leaf "HOLDS" s!"⊨ {n.claimS ca}" true, leaf "HOLDS" s!"⊨ {n.claimS cb}" true,
             leaf "RULE" s!"{n.litS la} ⇒ {n.litS lb}" true])
        | _, _ => none
      | .event _, .event _ => some (.mk "BUT-FOR" concl true
          [leaf "WITHOUT" s!"take out {w l.a}'s event, and {w l.b}'s is not possible or has no reason" true])
      | .event _, _ => some (.mk "BUT-FOR" concl true
          [leaf "WITHOUT" s!"take out {w l.a}'s event, and {w l.b} no longer holds" true])
      | _, .event _ => some (.mk "REASON" concl true
          [leaf "BELIEVES" s!"whoever acts at {w l.b} believes {w l.a}'s fact then" true])
      | _, _ => none
    match ways.head? with
    | some d => d
    | none => .mk "CAUSE" concl false [leaf "NOT-BORNE-OUT" "no lore, counterfactual or reason connects them" false]
  | .purpose =>
    let ok := ja.any fun j => match j.kind with | .goal _ => true | _ => false
    .mk "PURPOSE" concl ok [leaf "GOAL" s!"{w l.a} is read as a goal" ok]
  | .concession =>
    let ok := (ja ++ jb).all (ParaCtx.holds c)
    .mk "BOTH" concl ok [leaf "HOLDS" s!"{w l.a} holds" ok, leaf "HOLDS" s!"{w l.b} holds" ok]
  | .condition =>
    let ok := ja.any fun j => j.kind == .hypothetical
    .mk "CONDITION" concl ok [leaf "HYPOTHETICAL" s!"{w l.a} is hypothetical" ok]

def modDeriv (sp : Spec) (toks : List String) (m : Modifier) : Deriv :=
  let isTrait := match m.of, Trait.ofString? m.word with
    | some ch, some t => (sp.chars[ch]?.map fun (cs : CharSpec) => cs.traits.contains t).getD false
    | _, _ => false
  let concl := s!"‘{toks.getD m.at_ m.word}’ is accounted for"
  match m.of with
  | some ch =>
    if isTrait then .mk "TRAIT" concl true [leaf "PERSONA" s!"{(sp.chars[ch]?.map CharSpec.name).getD "?"} is {m.word}" true]
    else .mk "IMPRESSION" concl (m.sense == some "impression")
      [leaf "SENSE" (if m.sense == some "impression" then "a point-of-view judgement" else "not a trait, and not marked impression")
        (m.sense == some "impression")]
  | none =>
    let ok := (m.sense.map modSenses.contains).getD false
    .mk "SENSE" concl ok [leaf "SENSE" (m.sense.getD "no sense") ok]

/-- Every derivation of a paragraph, in token order. -/
def derivations (c : ParaCtx s) (f : TreeFacts) (js : List Judge) (toks : List String) : List (Nat × Deriv) :=
  ((f.preds.map fun p => (p.at_, clauseDeriv c f js toks p)) ++
   (f.links.filter (fun l => l.a != l.b)).map (fun l => (l.at_, linkDeriv c js toks l)) ++
   f.mods.map fun m => (m.at_, modDeriv s toks m)).mergeSort (fun a b => a.1 ≤ b.1)

end LangLib.Studio
