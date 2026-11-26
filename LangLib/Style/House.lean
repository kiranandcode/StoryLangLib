import LangLib.Style.Academic

/-!
# House style: Kiran's writing rules as decidable predicates

The author's house style (`writelikeme`: a list of LLM-isms and writing rules)
and a clarity check (after Williams and Bizup: every sentence is a story of
characters doing actions), stated in full in this file,
stated over checked trees, the story's declared lexicon and the paper's
lore. Nothing is read off raw strings: word classes live in `lexicon.json`
(`cls`), and what needs an argument (antithesis, unsupported claims, coined
terms used before they are defined) is decided in `World/Argument.lean`.

As in `Academic.lean`, `hsentOf` reads each sentence tree once into a flat
record (`HSent`, run by the CLI), and every rule is structural recursion over
the records, the academic records and the lore, so the verdicts are proved by
`decide +kernel`.

**Clarity** (the three faults):

* *hidden characters*: agentless passives (a `be` auxiliary with a
  participle head that is not an `ing` form, and no `by` agent);
* *hidden actions*: a subject whose head noun is a `nominal` (an action with
  a verb behind it) with a `light` verb or a copula ("A request was made");
* *inanimate actors*: an `object`, `abstract` or `place` entity as the subject of an
  active `animate` verb, including one of several coordinated predicates
  ("8 stages will close it");
* *vague wording*: noun stacks (three nouns in a row in a phrase that names no
  tracked entity: "grape availability request", not "proof repair tool");
* *misplaced emphasis*: the subject starts twelve or more words in, or a
  long sentence (35 words or more) stacks a parenthetical and a relative
  clause.

**LLM-isms**: slop emphasis (a sentence of six words or fewer with a
`significance` word), throat-clearing (`throat` expressions), understated
inflation (an `inflation` expression in a copular sentence), tricolons with
semicolons (two or more semicolons outside parentheticals),
deferred assertion (a copular sentence with a `wh` free relative: "what is
needed is"), emphatic clefts (expletive "it", a copula and a `that` clause),
observation-and-response joins (", and" before a clause with its own
subject), mechanical tetracola (four or more coordinated clauses),
sentence-initial conjunctions, `buzz` words, intensifiers, American
spellings (`us`), appositive-trailing cadence (an appositive followed by a
trailing adverbial clause), dramatic terminal sentences (a paragraph's last
sentence of eight words or fewer that negates or asserts significance),
summarising pivots (a short sentence whose subject is a composite),
summary closers (a paragraph's last sentence adds no entity), bare pivot
bridges (a paragraph opening on a contrast connective without restating the
last paragraph), spurious contrasts (a contrast connective with nothing in
the previous sentence to contrast), non-sequitur stacks (neighbouring
sentences sharing no entity and joined by no connective), and bare
post-modifying relative clauses: a noun phrase restricted by a relative
clause (`relcl`, or `acl` with a finite verb) whose verb has nothing past its
subject and the gap ("code that AI writes", "papers people cite"), so the
clause sets up a description and drops it. A clause with an object, a
complement, a purpose, a PP or an adverbial is extended, not bare ("code that
AI writes to kill puppies", "the tools we use every day"); clefts,
existentials and quotations are exempt. Two more from Wikipedia's "Signs of
AI writing" (negative parallelisms; undue emphasis on significance): a
negation followed by a dash and a fresh clause's subject ("isn't just
sourcing—it's framing"), which has no contrast connective for the academic
not-X-but-Y rule to see, and a `significance` modifier on a `vague` head noun
("marking a pivotal moment", "a significant shift"), or a `significance`
noun heading a subject ("Its significance extends beyond ..."). From the
same guide and the Sports Illustrated and Vanderbilt texts in `docs/deslop`:
vague attributions (an agentless passive of an `attribution` verb of
reputation, "is seen as a bridge", or a `weasel` phrase, "experts say", in a
sentence that cites nothing), `filler` phrases ("a
multitude of", "the importance of"), manufactured enthusiasm (`hype`:
"thrilled to bring you"), exhortations (the authors or the reader as subject
with a `deontic` word, "we must continue to engage"; at most one sentence in
twenty), and broader-trend claims (a `scope` modifier on a `trend` noun, "a
broader movement"). A contraction in class `fusedbe` ("that's", "they're")
counts as a copula or a passive auxiliary. Non-restrictive clauses ("X, which
people use,") are counted apart and not judged: set off by a comma or bracket
they assert a second proposition about a noun already identified, rather
than restricting it and leaving the description unsaid. Em-dashes, colon
setups, antitheses and rhetorical questions are in `Academic.lean`.
-/

namespace LangLib.Style.House
open LangLib LangLib.Style.Academic

structure HSent where
  para : Nat := 0
  words : Nat := 0
  heading : Bool := false
  clauses : Nat := 0
  passives : Nat := 0
  agentless : Nat := 0
  hiddenAction : Nat := 0
  inanimate : Nat := 0
  nounStacks : Nat := 0
  stacked : Bool := false
  semicolons : Nat := 0
  significance : Nat := 0
  intensifiers : Nat := 0
  buzz : Nat := 0
  usSpelling : Nat := 0
  throat : Nat := 0
  inflation : Nat := 0
  pseudoCleft : Bool := false
  itCleft : Bool := false
  andJoin : Bool := false
  /-- the most clause conjuncts in one coordination -/
  conjuncts : Nat := 0
  initialConj : Bool := false
  opensContrast : Bool := false
  trailingCadence : Bool := false
  /-- restrictive relative clauses that stop at the noun ("code that AI writes") -/
  bareRelatives : Nat := 0
  /-- non-restrictive ones that are equally bare (counted, not judged) -/
  bareAsides : Nat := 0
  /-- "not just X—it's Y": a negation, then a dash before a clause's subject -/
  negDash : Bool := false
  /-- "a pivotal moment": a `significance` modifier on a `vague` head noun -/
  abstractSig : Nat := 0
  /-- "is seen as a bridge": an agentless passive of an `attribution` verb, or a `weasel` phrase -/
  weasel : Nat := 0
  /-- "a multitude of", "the importance of": `filler` phrases -/
  filler : Nat := 0
  /-- "thrilled to bring you": `hype` words -/
  hype : Nat := 0
  /-- a `deontic` word ("must", "should", "let us"); an exhortation when the subject is the authors or the reader -/
  deontic : Bool := false
  /-- "a broader movement": a `scope` modifier on a `trend` head noun -/
  trend : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-! ## Reading one sentence -/

private def leafHas (lx : Lex) (c : String) : Tree → Bool
  | .leaf w => lx.has w c
  | _ => false

private def isClauseNode (t : Tree) : Bool := match t with
  | .node i _ => i.cat == .S || i.cat == .SBAR || hasSubj t
  | _ => false

/-- The head verb leaf of a clause node: a direct head `VERB`, else that of its head `VP`. -/
private partial def headVerb : Tree → Option Word
  | .leaf w => if w.upos == .VERB then some w else none
  | .node _ kids =>
    (kids.findSome? fun k => match k with
      | .leaf w => if w.upos == .VERB && w.role == some .head then some w else none
      | _ => none) <|>
    kids.findSome? fun k => match k with
      | .node j _ => if j.role == some .head && (j.cat == .VP || j.cat == .S) then headVerb k else none
      | _ => none

/-- The head noun of a phrase. -/
private partial def headNoun : Tree → Option Word
  | .leaf w => if w.upos == .NOUN then some w else none
  | .node _ kids =>
    (kids.findSome? fun k => match k with
      | .leaf w => if w.upos == .NOUN && w.role == some .head then some w else none
      | _ => none) <|>
    kids.findSome? fun k => match k with
      | .node j _ => if j.role == some .head then headNoun k else none
      | _ => none

structure Counts where
  clauses : Nat := 0
  passives : Nat := 0
  agentless : Nat := 0
  hiddenAction : Nat := 0
  inanimate : Nat := 0
  nounStacks : Nat := 0
  conjuncts : Nat := 0
  weasel : Nat := 0
  deriving Inhabited

def Counts.add (a b : Counts) : Counts :=
  { clauses := a.clauses + b.clauses, passives := a.passives + b.passives,
    agentless := a.agentless + b.agentless, hiddenAction := a.hiddenAction + b.hiddenAction,
    inanimate := a.inanimate + b.inanimate, nounStacks := a.nounStacks + b.nounStacks,
    conjuncts := max a.conjuncts b.conjuncts, weasel := a.weasel + b.weasel }

private def feat' (w : Word) (k : String) : Option String := (w.feats.find? (·.1 == k)).map (·.2)

/-- A `by` phrase among the kids or one level down. -/
private partial def hasAgent (lx : Lex) : List Tree → Bool
  | [] => false
  | k :: ks => (match k with
      | .node j kk => (j.cat == .PP && kk.any (leafHas lx "agent")) ||
          (j.cat == .VP && hasAgent lx kk)
      | _ => false) || hasAgent lx ks

private partial def counts (lx : Lex) (kinds : List (String × EntityKind)) : Tree → Counts
  | .leaf _ => {}
  | .node info kids =>
    let below : Counts := kids.foldl (fun (a : Counts) k => a.add (counts lx kinds k)) {}
    let verb := kids.findSome? fun k => match k with
      | .leaf w => if w.upos == .VERB && w.role == some .head then some w else none
      | _ => none
    let cop := kids.any (roleIs · .cop)
    let clause := verb.isSome || cop
    -- passive: a `be` auxiliary and a participle head here that is not an -ing form
    -- a contraction that carries "be" ("they're labelled") is the auxiliary too
    let passive := kids.any (fun k => (roleIs k .aux && leafHas lx "be" k) || leafHas lx "fusedbe" k) &&
      (match verb with
        | some w => feat' w "VerbForm" == some "Part" && !lx.has w "ing"
        | none => false)
    let agent := hasAgent lx kids
    let subj := kids.find? (roleIs · .nsubj)
    let subjVerb := verb <|> (kids.findSome? fun k => match k with
      | .node j _ => if j.role == some .head then headVerb k else none
      | _ => none)
    let hidden := match subj with
      | some sn => ((headNoun sn).map (lx.has · "nominal")).getD false &&
          (cop || (subjVerb.map (lx.has · "light")).getD false)
      | none => false
    -- the verbs of coordinated active predicates ("They are considered X and serve as Y")
    let conjVerbs : List Word := kids.flatMap fun k => match k with
      | .node j kk => if j.role == some .head && j.cat == .COORD then
          kk.filterMap fun c => match c with
            | .node _ ck => if roleIs c .conj && !ck.any (fun x => roleIs x .aux && leafHas lx "be" x)
                then headVerb c else none
            | _ => none
        else []
      | _ => []
    -- a passive one level down, in the head verb phrase ("X should not be interpreted")
    let headPassive := kids.any fun k => match k with
      | .node j kk => j.role == some .head && kk.any (fun x => roleIs x .aux && leafHas lx "be" x) &&
          (match headVerb k with
            | some w => feat' w "VerbForm" == some "Part" && !lx.has w "ing"
            | none => false)
      | _ => false
    -- the subject of a passive is not its actor
    let inanimateHere : Bool := !passive && !headPassive && match subj.bind refOf with
      | some e => ((kinds.lookup e).map (fun k => k == .object || k == .abstract || k == .place)).getD false &&
          ((subjVerb.toList ++ conjVerbs).any (lx.has · "animate"))
      | none => false
    let nouns := kids.foldl (fun (run, best) k => match k with
      | .leaf w => if w.upos == .NOUN || w.upos == .PROPN then (run + 1, max best (run + 1)) else (0, best)
      | _ => (0, best)) (0, 0)
    -- a stack that names a tracked entity ("proof repair tool") is a term, not vague wording
    let stack := info.cat == .NP && nouns.2 ≥ 3 && info.ref.isNone
    let conj := (kids.filter fun k => roleIs k .conj && isClauseNode k).length
    let here : Counts :=
      { clauses := if clause then 1 else 0,
        passives := if passive then 1 else 0,
        agentless := if passive && !agent then 1 else 0,
        hiddenAction := if hidden then 1 else 0,
        inanimate := if inanimateHere then 1 else 0,
        nounStacks := if stack then 1 else 0,
        conjuncts := if conj > 0 then conj + 1 else 0,
        weasel := if passive && !agent && (verb.map (lx.has · "attribution")).getD false then 1 else 0 }
    below.add here

/-- Roles that extend a relative clause past "noun + subject + verb": an object,
a complement, a purpose or infinitive, a PP, an adverbial. -/
def extensionRoles : List Role :=
  [.obj, .iobj, .ccomp, .xcomp, .obl, .advcl, .advmod, .nmod, .csubj, .dep]

/-- The dependents of a clause's verb: its kids and, down the chain of heads,
theirs. `none` when the head is not a verb (a copular predicate: "which are a
form of ..." describes, so it is not bare). -/
private partial def clauseDeps : Tree → Option (List Tree)
  | .leaf _ => none
  | .node _ kids =>
    let headNode := kids.find? fun k => match k with
      | .node j _ => j.role == some .head | _ => false
    let headLeaf := kids.find? fun k => match k with
      | .leaf w => w.role == some .head | _ => false
    match headLeaf, headNode with
    | some (.leaf w), _ => if w.upos == .VERB then some kids else none
    | _, some h =>
      match h with
      | .node j _ => if j.cat == .VP || j.cat == .S then (clauseDeps h).map (kids ++ ·) else none
      | _ => none
    | _, _ => none

/-- A relative clause that only restricts its noun: its verb has nothing past
its subject and the gap (the relative pronoun, if it is the object). -/
private def bareClause (lx : Lex) (rc : Tree) : Bool :=
  let first := (leavesOf rc).filter isWord |>.head?
  let isRelPron (k : Tree) := match k with
    | .leaf w => w.upos == .PRON && (lx.has w "that" || lx.has w "wh") &&
        (some w.form == first.map (·.form))
    | _ => false
  match clauseDeps rc with
  | none => false
  | some deps => !deps.any fun k => !isRelPron k && ((roleOf k).map extensionRoles.contains).getD false

private def finiteHead (t : Tree) : Bool := match t with
  | .node _ kids => (kids.any fun k => match k with
      | .leaf w => (w.upos == .VERB || w.upos == .AUX) && (w.feats.find? (·.1 == "VerbForm")).map (·.2) == some "Fin"
      | _ => false) || match headVerb t with
      | some w => (w.feats.find? (·.1 == "VerbForm")).map (·.2) == some "Fin"
      | none => false
  | _ => false

/-- Bare relative clauses in noun phrases, outside quotations: (restrictive,
non-restrictive). A relative is a `relcl`, or an `acl` with a finite verb; it
is non-restrictive when set off by a comma or bracket. -/
private partial def bareRelativesIn (lx : Lex) : Tree → Nat × Nat
  | .leaf _ => (0, 0)
  | .node i kids =>
    if i.cat == .QUOTE then (0, 0) else
    let arr := kids.toArray
    let here := if i.cat != .NP then (0, 0) else
      (List.range arr.size).foldl (fun (r, n) j =>
        let k := arr[j]!
        let rel := roleIs k .relcl || (roleIs k .acl && finiteHead k)
        if !rel || !bareClause lx k then (r, n) else
        let setOff := (j > 0 && match arr[j - 1]! with
            | .leaf w => w.form == "," || w.form == "(" | _ => false) ||
          (match k with | .node _ (.leaf w :: _) => w.upos == .PUNCT | _ => false)
        if setOff then (r, n + 1) else (r + 1, n)) (0, 0)
    kids.foldl (fun (a, b) k => let (c, d) := bareRelativesIn lx k; (a + c, b + d)) here

/-- Semicolons outside parentheticals (citations separate their entries with them). -/
private partial def clauseSemicolons : Tree → Nat
  | .leaf w => if w.form == ";" then 1 else 0
  | .node i kids => if i.cat == .PRN then 0 else kids.foldl (fun n k => n + clauseSemicolons k) 0

private partial def hasCat (c : Cat) : Tree → Bool
  | .leaf _ => false
  | .node i kids => i.cat == c || kids.any (hasCat c)

private partial def hasRole (r : Role) : Tree → Bool
  | .leaf w => w.role == some r
  | .node i kids => i.role == some r || kids.any (hasRole r)

/-- How many times a multiword expression of class `c` occurs in the forms. -/
def mweCount (lx : Lex) (c : String) (forms : List String) : Nat :=
  let arr := forms.toArray
  (lx.mweCls.filter (·.2 == c)).foldl (fun n (ks, _) =>
    n + ((List.range arr.size).filter fun i => ks.zipIdx.all fun (k, j) => arr[i + j]? == some k).length) 0

private def firstLeaf? (t : Tree) : Option Word := ((leavesOf t).filter isWord).head?

/-- A parenthetical with a number in it: a citation ("(Klein et al. 2009)"). -/
private partial def cited : Tree → Bool
  | .leaf _ => false
  | .node i kids => (i.cat == .PRN && (leavesOf (.node i kids)).any (·.upos == .NUM)) || kids.any cited

/-- Leaves outside quotations. -/
private partial def unquotedLeaves : Tree → List Word
  | .leaf w => [w]
  | .node i kids => if i.cat == .QUOTE then [] else kids.flatMap unquotedLeaves

/-- A negation, later a dash, and right after the dash a clause's subject:
"isn't just sourcing—it's framing". -/
def negDashIn (lx : Lex) (ls : List Word) : Bool :=
  let arr := ls.toArray
  let isDash (w : Word) := w.form == "—" || w.form == "–" || w.form == "--"
  (List.range arr.size).any fun i => lx.is arr[i]! "neg" &&
    (List.range arr.size).any fun j => i < j && isDash arr[j]! &&
      ((arr[j + 1]?.map fun w => w.role == some .nsubj || w.role == some .expl).getD false)

/-- Noun phrases whose head is a `vague` noun modified by a `significance`
word: "a pivotal moment", "a significant shift", "a crucial role". -/
private partial def abstractSigIn (lx : Lex) : Tree → Nat
  | .leaf _ => 0
  | .node i kids =>
    -- a PP whose object noun is a direct kid counts as that noun phrase
    let here := if i.cat != .NP && i.cat != .PP then 0 else
      match headNoun (.node i kids) with
      | some n => if (lx.has n "vague" && kids.any (fun k => roleIs k .amod &&
            (leavesOf k).any (lx.has · "significance"))) ||
            -- "Its significance extends beyond ...", "The importance of X is ..."
            (i.role == some .nsubj && lx.has n "significance") then 1 else 0
      | none => 0
    here + kids.foldl (fun a k => a + abstractSigIn lx k) 0

/-- Noun phrases whose head is a `trend` noun modified by a `scope` word:
"a broader movement", "a growing trend", "the wider landscape". -/
private partial def trendIn (lx : Lex) : Tree → Nat
  | .leaf _ => 0
  | .node i kids =>
    let here := if i.cat != .NP && i.cat != .PP then 0 else
      match headNoun (.node i kids) with
      | some n => if lx.has n "trend" && kids.any (fun k => roleIs k .amod &&
            (leavesOf k).any (lx.has · "scope")) then 1 else 0
      | none => 0
    here + kids.foldl (fun a k => a + trendIn lx k) 0

def hsentOf (lx : Lex) (kinds : List (String × EntityKind)) (para : Nat) (t : Tree) : HSent :=
  let ls := leavesOf t
  let ws := ls.filter isWord
  let forms := ls.map (lower ·.form)
  let heading : Bool := match t with | .node i _ => i.cat == .FRAG | .leaf _ => true
  let c := counts lx kinds t
  let rootKids := match t with | .node _ kk => kk | .leaf _ => []
  let cls (k : String) := (ws.filter (lx.has · k)).length + mweCount lx k forms
  let copular := rootKids.any (roleIs · .cop) || rootKids.any (leafHas lx "fusedbe") ||
    rootKids.any fun k => match k with
    | .node j kk => j.role == some .head && (kk.any (roleIs · .cop) || kk.any (leafHas lx "fusedbe")) | _ => false
  let whClause := rootKids.any fun k => isClauseNode k && ((firstLeaf? k).map (lx.has · "wh")).getD false
  let thatClause := rootKids.any fun k => match k with
    | .node _ kk => kk.any (fun x => isClauseNode x && ((firstLeaf? x).map (lx.has · "that")).getD false) ||
        (isClauseNode k && ((firstLeaf? k).map (lx.has · "that")).getD false)
    | _ => false
  let joinIn (kk : List Tree) : Bool :=
    (List.range kk.length).any fun i =>
      (kk[i]?.map (leafHas lx "and")).getD false && ((kk[i]?.map (roleIs · .cc)).getD false) &&
      ((kk[i + 1]?.map fun x => roleIs x .conj && hasSubj x).getD false)
  let headKids := rootKids.flatMap fun k => match k with
    | .node j kk => if j.role == some .head && j.cat == .COORD then kk else []
    | _ => []
  let lastContent := (rootKids.filter fun k => match k with | .leaf w => isWord w | _ => true).getLast?
  { para, words := ws.length, heading,
    clauses := c.clauses, passives := c.passives, agentless := c.agentless,
    hiddenAction := c.hiddenAction, inanimate := c.inanimate, nounStacks := c.nounStacks,
    stacked := ws.length ≥ 35 && hasCat .PRN t && (hasRole .relcl t || hasRole .acl t),
    semicolons := clauseSemicolons t,
    significance := cls "significance", intensifiers := cls "intensifier", buzz := cls "buzz",
    usSpelling := cls "us", throat := cls "throat",
    -- "This is more than X": inflation only predicated by a copula
    inflation := if copular then cls "inflation" else 0,
    pseudoCleft := copular && whClause,
    itCleft := rootKids.any (roleIs · .expl) && copular && thatClause,
    andJoin := joinIn rootKids || joinIn headKids,
    conjuncts := c.conjuncts,
    initialConj := ((ws.head?.map (·.upos == .CCONJ)).getD false),
    opensContrast := ((ws.head?.map fun w => lx.is w "contrast" || lx.is w "concession")).getD false,
    -- clefts ("it is X that ...") and existentials ("there is X that ...") are exempt
    bareRelatives := if rootKids.any (roleIs · .expl) then 0 else (bareRelativesIn lx t).1,
    bareAsides := if rootKids.any (roleIs · .expl) then 0 else (bareRelativesIn lx t).2,
    negDash := negDashIn lx (unquotedLeaves t),
    abstractSig := abstractSigIn lx t,
    -- a sentence that cites its source ("(Klein et al. 2009)") attributes, it does not weasel
    weasel := if cited t then 0 else c.weasel + cls "weasel",
    filler := cls "filler",
    hype := cls "hype",
    deontic := cls "deontic" > 0,
    trend := trendIn lx t,
    trailingCadence := rootKids.any (roleIs · .appos) &&
      ((lastContent.map fun k => roleIs k .advcl || (roleIs k .obl && isClauseNode k)).getD false) }

/-! ## Features (structural, kernel-friendly) -/

def sumH (f : HSent → Nat) : List HSent → Nat
  | [] => 0
  | s :: ss => f s + sumH f ss

def countH (p : HSent → Bool) : List HSent → Nat
  | [] => 0
  | s :: ss => (if p s then 1 else 0) + countH p ss

/-- Neighbours in one paragraph: (previous, next), with the house records. -/
def pairs : List (ASent × HSent) → List ((ASent × HSent) × (ASent × HSent))
  | a :: b :: rest => (a, b) :: pairs (b :: rest)
  | _ => []

def shares (a b : ASent) : Bool := (names a).any fun e => !given.contains e && (names b).contains e

structure HFeatures where
  sents : Nat
  clauses : Nat
  agentless : Nat
  passives : Nat
  hiddenAction : Nat
  inanimate : Nat
  nounStacks : Nat
  buried : Nat
  stacked : Nat
  slopEmphasis : Nat
  throat : Nat
  inflation : Nat
  tricolons : Nat
  pseudoClefts : Nat
  itClefts : Nat
  andJoins : Nat
  tetracola : Nat
  initialConj : Nat
  buzz : Nat
  intensifiers : Nat
  usSpelling : Nat
  trailingCadence : Nat
  dramaticTerminal : Nat
  summarisingPivots : Nat
  summaryClosers : Nat
  barePivots : Nat
  spuriousContrasts : Nat
  nonSequiturs : Nat
  bareRelatives : Nat
  bareAsides : Nat
  negDashes : Nat
  abstractSig : Nat
  weasels : Nat
  fillers : Nat
  hype : Nat
  exhortations : Nat
  trendClaims : Nat
  deriving Repr, DecidableEq, Inhabited

def HFeatures.ofSents (lo : ALore) (as : List ASent) (hs : List HSent) : HFeatures :=
  let both := as.zip hs
  let ps := groupParas as
  -- paragraphs of (academic, house) records, in order
  let paras : List (List (ASent × HSent)) :=
    (ps.foldl (fun (acc, rest) p => (acc ++ [rest.take p.length], rest.drop p.length)) (([] : List (List (ASent × HSent))), both)).1
  let body (p : List (ASent × HSent)) := p.filter (!·.2.heading)
  let lastOf (p : List (ASent × HSent)) := (body p).getLast?
  let inPara := paras.flatMap fun p => pairs (body p)
  let prevParaEnts : List (List String × List (ASent × HSent)) :=
    (paras.foldl (fun (acc, prev) p => (acc ++ [(prev, p)], p.flatMap fun x => names x.1)) (([] : List (List String × List (ASent × HSent))), ([] : List String))).1
  let isComposite (e : String) : Bool := lo.comps.any (·.1 == e)
  { sents := hs.length, clauses := sumH (·.clauses) hs,
    agentless := sumH (·.agentless) hs, passives := sumH (·.passives) hs,
    hiddenAction := sumH (·.hiddenAction) hs, inanimate := sumH (·.inanimate) hs,
    nounStacks := sumH (·.nounStacks) hs,
    buried := (both.filter fun (a, h) => !h.heading && a.subj.isSome && a.subjAt ≥ 12).length,
    stacked := countH (·.stacked) hs,
    slopEmphasis := countH (fun h => !h.heading && h.words ≤ 6 && h.significance > 0) hs,
    throat := sumH (·.throat) hs, inflation := sumH (·.inflation) hs,
    tricolons := countH (·.semicolons ≥ 2) hs,
    pseudoClefts := countH (·.pseudoCleft) hs, itClefts := countH (·.itCleft) hs,
    andJoins := countH (·.andJoin) hs, tetracola := countH (·.conjuncts ≥ 4) hs,
    initialConj := countH (·.initialConj) hs,
    buzz := sumH (·.buzz) hs, intensifiers := sumH (·.intensifiers) hs, usSpelling := sumH (·.usSpelling) hs,
    trailingCadence := countH (·.trailingCadence) hs,
    dramaticTerminal := (paras.filter fun p => (body p).length ≥ 2 && match lastOf p with
      | some (a, h) => h.words ≤ 8 && (a.negated || h.significance > 0)
      | none => false).length,
    summarisingPivots := (both.filter fun (a, h) => !h.heading && h.words ≤ 10 &&
      ((a.subj.map isComposite).getD false)).length,
    summaryClosers := (paras.filter fun p => (body p).length ≥ 3 && match lastOf p with
      | some (a, _) =>
        let earlier := ((body p).dropLast).flatMap fun x => names x.1
        let own := (names a).filter (!given.contains ·)
        !own.isEmpty && own.all earlier.contains
      | none => false).length,
    barePivots := (prevParaEnts.filter fun (prev, p) => match (body p).head? with
      | some (a, h) => h.opensContrast && !prev.isEmpty && !(names a).any fun e => !given.contains e && prev.contains e
      | none => false).length,
    spuriousContrasts := (inPara.filter fun ((a, _), (b, hb)) => hb.opensContrast && !shares a b).length,
    nonSequiturs := (inPara.filter fun ((a, _), (b, hb)) =>
      !shares a b && !b.frame && !b.causal && !b.recalls && !hb.opensContrast &&
      !(b.subj.map isComposite).getD false).length,
    bareRelatives := sumH (·.bareRelatives) hs, bareAsides := sumH (·.bareAsides) hs,
    negDashes := countH (·.negDash) hs, abstractSig := sumH (·.abstractSig) hs,
    weasels := sumH (·.weasel) hs, fillers := sumH (·.filler) hs, hype := sumH (·.hype) hs,
    exhortations := (both.filter fun (a, h) => h.deontic && ((a.subj.map given.contains).getD false)).length,
    trendClaims := sumH (·.trend) hs }

/-! ## Rules and styles -/

inductive HFeat where
  | sents | clauses | agentless | passives | hiddenAction | inanimate | nounStacks | buried | stacked
  | slopEmphasis | throat | inflation | tricolons | pseudoClefts | itClefts | andJoins | tetracola
  | initialConj | buzz | intensifiers | usSpelling | trailingCadence | dramaticTerminal
  | summarisingPivots | summaryClosers | barePivots | spuriousContrasts | nonSequiturs
  | bareRelatives | bareAsides | negDashes | abstractSig
  | weasels | fillers | hype | exhortations | trendClaims
  deriving Repr, DecidableEq, Inhabited

def HFeatures.get (f : HFeatures) : HFeat → Nat
  | .sents => f.sents | .clauses => f.clauses | .agentless => f.agentless | .passives => f.passives
  | .hiddenAction => f.hiddenAction | .inanimate => f.inanimate | .nounStacks => f.nounStacks
  | .buried => f.buried | .stacked => f.stacked | .slopEmphasis => f.slopEmphasis
  | .throat => f.throat | .inflation => f.inflation | .tricolons => f.tricolons
  | .pseudoClefts => f.pseudoClefts | .itClefts => f.itClefts | .andJoins => f.andJoins
  | .tetracola => f.tetracola | .initialConj => f.initialConj | .buzz => f.buzz
  | .intensifiers => f.intensifiers | .usSpelling => f.usSpelling
  | .trailingCadence => f.trailingCadence | .dramaticTerminal => f.dramaticTerminal
  | .summarisingPivots => f.summarisingPivots | .summaryClosers => f.summaryClosers
  | .barePivots => f.barePivots | .spuriousContrasts => f.spuriousContrasts
  | .nonSequiturs => f.nonSequiturs
  | .bareRelatives => f.bareRelatives | .bareAsides => f.bareAsides
  | .negDashes => f.negDashes | .abstractSig => f.abstractSig
  | .weasels => f.weasels | .fillers => f.fillers | .hype => f.hype
  | .exhortations => f.exhortations | .trendClaims => f.trendClaims

def HFeat.name : HFeat → String
  | .sents => "sents" | .clauses => "clauses" | .agentless => "agentless" | .passives => "passives"
  | .hiddenAction => "hiddenAction" | .inanimate => "inanimate" | .nounStacks => "nounStacks"
  | .buried => "buried" | .stacked => "stacked" | .slopEmphasis => "slopEmphasis"
  | .throat => "throat" | .inflation => "inflation" | .tricolons => "tricolons"
  | .pseudoClefts => "pseudoClefts" | .itClefts => "itClefts" | .andJoins => "andJoins"
  | .tetracola => "tetracola" | .initialConj => "initialConj" | .buzz => "buzz"
  | .intensifiers => "intensifiers" | .usSpelling => "usSpelling"
  | .trailingCadence => "trailingCadence" | .dramaticTerminal => "dramaticTerminal"
  | .summarisingPivots => "summarisingPivots" | .summaryClosers => "summaryClosers"
  | .barePivots => "barePivots" | .spuriousContrasts => "spuriousContrasts"
  | .nonSequiturs => "nonSequiturs"
  | .bareRelatives => "bareRelatives" | .bareAsides => "bareAsides"
  | .negDashes => "negDashes" | .abstractSig => "abstractSig"
  | .weasels => "weasels" | .fillers => "fillers" | .hype => "hype"
  | .exhortations => "exhortations" | .trendClaims => "trendClaims"

def HFeat.all : List HFeat :=
  [.sents, .clauses, .agentless, .passives, .hiddenAction, .inanimate, .nounStacks, .buried, .stacked,
   .slopEmphasis, .throat, .inflation, .tricolons, .pseudoClefts, .itClefts, .andJoins, .tetracola,
   .initialConj, .buzz, .intensifiers, .usSpelling, .trailingCadence, .dramaticTerminal,
   .summarisingPivots, .summaryClosers, .barePivots, .spuriousContrasts, .nonSequiturs,
   .bareRelatives, .bareAsides, .negDashes, .abstractSig,
   .weasels, .fillers, .hype, .exhortations, .trendClaims]

inductive HRule where
  | atMost (f : HFeat) (n : Nat)
  /-- `num / den ≤ p / q` -/
  | ratioAtMost (num den : HFeat) (p q : Nat)
  deriving Repr, DecidableEq, Inhabited

def HRule.holds (f : HFeatures) : HRule → Bool
  | .atMost x n => f.get x ≤ n
  | .ratioAtMost a b p q => f.get a * q ≤ p * f.get b

def HRule.show : HRule → String
  | .atMost x n => s!"{x.name} ≤ {n}"
  | .ratioAtMost a b p q => s!"{a.name} / {b.name} ≤ {p}/{q}"

structure HStyle where
  name : String
  rules : List (String × HRule)

def HStyle.failing (st : HStyle) (f : HFeatures) : List String :=
  (st.rules.filter fun (_, r) => !r.holds f).map (·.1)

/-- The clarity check: characters as subjects, actions as verbs, plain words,
the point first. Ratios are judgement calls. -/
def clarity : HStyle where
  name := "clarity"
  rules := [
    ("characters: few agentless passives", .ratioAtMost .agentless .clauses 1 10),
    ("actions: few hidden in nouns", .ratioAtMost .hiddenAction .sents 1 20),
    ("no inanimate actors", .atMost .inanimate 0),
    ("few noun stacks", .ratioAtMost .nounStacks .sents 1 10),
    ("point first", .ratioAtMost .buried .sents 1 20),
    ("no stacked asides", .ratioAtMost .stacked .sents 1 20),
    ("no non-sequitur stacks", .ratioAtMost .nonSequiturs .sents 1 10)]

/-- The `/writelikeme` ban list, as far as trees and the lexicon show it. -/
def writeLikeMe : HStyle where
  name := "writelikeme"
  rules := [
    ("no slop emphasis", .atMost .slopEmphasis 0),
    ("no throat-clearing", .atMost .throat 0),
    ("no understated inflation", .atMost .inflation 0),
    ("no tricolon with semicolons", .atMost .tricolons 0),
    ("no deferred assertion", .atMost .pseudoClefts 0),
    ("no emphatic cleft", .atMost .itClefts 0),
    ("few observation-and-response joins", .ratioAtMost .andJoins .sents 1 10),
    ("no mechanical tetracolon", .atMost .tetracola 0),
    ("no sentence-initial conjunctions", .atMost .initialConj 0),
    ("no buzz words", .atMost .buzz 0),
    ("no empty intensifiers", .atMost .intensifiers 0),
    ("British spelling", .atMost .usSpelling 0),
    ("no appositive-trailing cadence", .atMost .trailingCadence 0),
    ("no dramatic terminal sentences", .atMost .dramaticTerminal 0),
    ("no summarising pivots", .atMost .summarisingPivots 0),
    ("no summary closers", .atMost .summaryClosers 0),
    ("no bare pivot bridges", .atMost .barePivots 0),
    ("no spurious contrasts", .atMost .spuriousContrasts 0),
    ("no bare relative clauses", .atMost .bareRelatives 0),
    ("no not-X-dash-Y", .atMost .negDashes 0),
    ("no abstract significance", .atMost .abstractSig 0),
    ("no vague attributions", .atMost .weasels 0),
    ("no filler phrases", .atMost .fillers 0),
    ("no manufactured enthusiasm", .atMost .hype 0),
    ("few exhortations", .ratioAtMost .exhortations .sents 1 20),
    ("no broader-trend claims", .atMost .trendClaims 0)]

def houseStyles : List HStyle := [clarity, writeLikeMe]

/-! ## `langlib house <dir>` -/

open Lean

def loadHSents (dir : String) : IO (List HSent) := do
  let lx ← loadLex dir
  let names := ((← System.FilePath.readDir s!"{dir}/paragraphs").map (·.fileName)).toList.filter isParaDoc
  let mut out : List HSent := []
  for n in names.mergeSort (· ≤ ·) do
    let para := (String.ofList (n.toList.take 2)).toNat!
    match docOfString (← IO.FS.readFile s!"{dir}/paragraphs/{n}") with
    | .ok d =>
      let kinds := d.entities.map fun e => (e.id, e.kind)
      out := out ++ d.sentences.map fun s => hsentOf lx kinds para s.tree
    | .error e => throw (IO.userError s!"{n}: {e}")
  pure out

/-- Where each rule bites (paragraph, sentence in it). The paragraph and
neighbour rules restate `HFeatures.ofSents` per sentence. -/
def hflagged (lo : ALore) (as : List ASent) (hs : List HSent) : Json :=
  let idx := (groupParas as).flatMap fun p => p.zipIdx.map fun (s, i) => (s.para, i + 1)
  let at_ (x : Nat × Nat) : Json := Json.arr #[toJson x.1, toJson x.2]
  let pick (p : HSent → Bool) := ((hs.zip idx).filter (p ·.1)).map (at_ ·.2)
  let both := (as.zip hs).zip idx
  let isComposite (e : String) : Bool := lo.comps.any (·.1 == e)
  let grp := (groupParas as).map fun p =>
    let n := (p.head?.map (·.para)).getD 0
    both.filter (·.1.1.para == n)
  let body (p : List ((ASent × HSent) × (Nat × Nat))) := p.filter (!·.1.2.heading)
  let pos (xs : List ((ASent × HSent) × (Nat × Nat))) : Json := Json.arr (xs.map (at_ ·.2)).toArray
  let nb := grp.flatMap fun p => (body p).zip ((body p).drop 1)
  let prevEnts := [] :: grp.map fun p => p.flatMap fun x => names x.1.1
  Json.mkObj [
    ("buried", pos (both.filter fun ((a, h), _) => !h.heading && a.subj.isSome && a.subjAt ≥ 12)),
    ("dramaticTerminal", pos (grp.filterMap fun p => if (body p).length < 2 then none else
      (body p).getLast?.filter fun ((a, h), _) => h.words ≤ 8 && (a.negated || h.significance > 0))),
    ("summarisingPivots", pos (both.filter fun ((a, h), _) => !h.heading && h.words ≤ 10 &&
      ((a.subj.map isComposite).getD false))),
    ("summaryClosers", pos (grp.filterMap fun p => if (body p).length < 3 then none else
      (body p).getLast?.filter fun ((a, _), _) =>
        let earlier := ((body p).dropLast).flatMap fun x => names x.1.1
        let own := (names a).filter (!given.contains ·)
        !own.isEmpty && own.all earlier.contains)),
    ("barePivots", pos ((grp.zip prevEnts).filterMap fun (p, prev) => (body p).head?.filter fun ((a, h), _) =>
      h.opensContrast && !prev.isEmpty && !(names a).any fun e => !given.contains e && prev.contains e)),
    ("spuriousContrasts", pos ((nb.filter fun ((x, _), ((b, hb), _)) => hb.opensContrast && !shares x.1 b).map (·.2))),
    ("nonSequiturs", pos ((nb.filter fun ((x, _), ((b, hb), _)) =>
      !shares x.1 b && !b.frame && !b.causal && !b.recalls && !hb.opensContrast &&
      !(b.subj.map isComposite).getD false).map (·.2))),
    ("agentless", Json.arr (pick (·.agentless > 0)).toArray),
    ("hiddenAction", Json.arr (pick (·.hiddenAction > 0)).toArray),
    ("inanimate", Json.arr (pick (·.inanimate > 0)).toArray),
    ("nounStacks", Json.arr (pick (·.nounStacks > 0)).toArray),
    ("stacked", Json.arr (pick (·.stacked)).toArray),
    ("slopEmphasis", Json.arr (pick fun h => h.words ≤ 6 && h.significance > 0).toArray),
    ("throat", Json.arr (pick (·.throat > 0)).toArray),
    ("inflation", Json.arr (pick (·.inflation > 0)).toArray),
    ("tricolons", Json.arr (pick (·.semicolons ≥ 2)).toArray),
    ("pseudoClefts", Json.arr (pick (·.pseudoCleft)).toArray),
    ("itClefts", Json.arr (pick (·.itCleft)).toArray),
    ("andJoins", Json.arr (pick (·.andJoin)).toArray),
    ("tetracola", Json.arr (pick (·.conjuncts ≥ 4)).toArray),
    ("initialConj", Json.arr (pick (·.initialConj)).toArray),
    ("buzz", Json.arr (pick (·.buzz > 0)).toArray),
    ("intensifiers", Json.arr (pick (·.intensifiers > 0)).toArray),
    ("usSpelling", Json.arr (pick (·.usSpelling > 0)).toArray),
    ("trailingCadence", Json.arr (pick (·.trailingCadence)).toArray),
    ("opensContrast", Json.arr (pick (·.opensContrast)).toArray),
    ("bareRelatives", Json.arr (pick (·.bareRelatives > 0)).toArray),
    ("bareAsides", Json.arr (pick (·.bareAsides > 0)).toArray),
    ("negDashes", Json.arr (pick (·.negDash)).toArray),
    ("abstractSig", Json.arr (pick (·.abstractSig > 0)).toArray),
    ("weasels", Json.arr (pick (·.weasel > 0)).toArray),
    ("fillers", Json.arr (pick (·.filler > 0)).toArray),
    ("hype", Json.arr (pick (·.hype > 0)).toArray),
    ("exhortations", pos (both.filter fun ((a, h), _) => h.deontic && ((a.subj.map given.contains).getD false))),
    ("trendClaims", Json.arr (pick (·.trend > 0)).toArray)]

def HFeatures.toJson (f : HFeatures) : Json :=
  Json.mkObj (HFeat.all.map fun x => (x.name, Lean.toJson (f.get x)))

def houseMain (dir : String) (opts : List String) : IO String := do
  let (as, lo, _) ← loadAll dir
  let hs ← loadHSents dir
  match opts with
  | ["--lean", name] =>
    let body := ",\n   ".intercalate (hs.map fun s => Std.Format.pretty (repr s) 1000)
    pure s!"def {name} : List HSent :=\n  [{body}]\n"
  | _ =>
    let f := HFeatures.ofSents lo as hs
    pure (Json.mkObj [
      ("features", f.toJson),
      ("flagged", hflagged lo as hs),
      ("styles", Json.arr (houseStyles.map fun st =>
        Json.mkObj [("name", st.name), ("failing", Json.arr ((st.failing f).map Json.str).toArray),
          ("rules", Json.arr (st.rules.map fun (n, r) =>
            Json.mkObj [("name", n), ("rule", r.show), ("holds", r.holds f)]).toArray)]).toArray)]).pretty

/-! ## A check on the rules themselves -/

namespace Toy
/-- "Proof repair is hard. And it matters." (emphasis, an initial conjunction,
a dramatic last line) then a paragraph opening on "However" without the last one's subject. -/
def as : List ASent :=
  [ { para := 1, words := 4, subj := some "repair", ents := [("repair", 0)] },
    { para := 1, words := 3, subj := some "repair", ents := [("repair", 1)] },
    { para := 2, words := 5, subj := some "sis", ents := [("sis", 1)] } ]
def hs : List HSent :=
  [ { para := 1, words := 4 },
    { para := 1, words := 3, significance := 1, initialConj := true },
    { para := 2, words := 5, opensContrast := true } ]
theorem toy_house :
    writeLikeMe.failing (HFeatures.ofSents {} as hs) =
      ["no slop emphasis", "no sentence-initial conjunctions", "no dramatic terminal sentences",
       "no bare pivot bridges"] := by
  decide +kernel
/-- "Sisyphus repairs the code that AI writes." -/
theorem toy_bare_relative :
    writeLikeMe.failing (HFeatures.ofSents {} [{ para := 1, words := 7 }] [{ para := 1, words := 7, bareRelatives := 1 }]) =
      ["no bare relative clauses"] := by
  decide +kernel
end Toy

end LangLib.Style.House
