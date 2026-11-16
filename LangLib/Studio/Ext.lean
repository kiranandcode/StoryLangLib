import Lean.Data.Json
import LangLib.Json
import LangLib.Studio.Parse
import LangLib.World.Care
import LangLib.World.Identity
import LangLib.World.Affect
import LangLib.Studio.Complete

/-!
# Ties, care and identity for a story directory

The Studio's world has places, minds, bonds and consent to intimacy. A story
can add a second reading per paragraph with the modules of `World/Ties`,
`World/Care` and `World/Identity`: in `paragraphs/NN.events.json`,

```
"ext": [{"e": "tend katsuki deku water", "at": 31, "w": "accept"},
        {"e": "learnPron katsuki deku she", "at": 3, "w": "girl"},
        {"e": "refer h1 deku he", "at": 1, "w": "He"}]
```

and `story.json` declares the vocabulary and the opening state under `"ext"`:
tie types and their laws, need kinds (and which need consent), the tie care
builds, the tie a shield answers, every character's names (kind, and the
trust needed to be told a private one), private facts, and who knows what.

Besides the events, the paragraph's **references** are checked against what
the referrer knows: every proper name and third-person pronoun (and gendered
noun: "boyfriend", "girl") that refers to a character. In narration the
referrer is the point-of-view character: a stranger is "they" until she says
she is a girl, and has no name until she gives one. In speech it is the
speaker: they may only use a name they know, and a pronoun that is not the
person's must be read as a `refer` event at that word, so the misgendering is
recorded (deliberate when the speaker knew better). Events at or before a
mention's token take effect before it is checked.

`langlib ext <dir>` prints the verdicts as JSON; `langlib ext <dir> --lean
<ns>` prints a Lean file whose theorems are proved by `decide +kernel`.
Characters are the Studio spec's, by index; names and secrets are strings.
-/

namespace LangLib.Studio
open Lean LangLib LangLib.World

structure TieSpec where
  id : String
  symmetric : Bool := false
  excludes : List Nat := []
  requires : Option (Nat × Nat) := none
  deriving Repr, DecidableEq

structure XSpec where
  chars : List String
  pron : List Pron
  ties : List TieSpec := []
  needs : List String := []
  consent : List (Nat × Consent) := []
  builds : Option Nat := none
  threat : Option Nat := none
  protects : Option Nat := none
  trust : Option Nat := none
  names : List (Nat × List (String × NameKind × Nat)) := []
  secrets : List (Nat × List (String × Nat)) := []
  startNeeds : List (Nat × Nat) := []
  startTies : List (Nat × Nat × Nat × Nat) := []
  startNames : List (Nat × Nat × String) := []
  startPron : List (Nat × Nat × Pron) := []
  startSecrets : List (Nat × Nat × String) := []
  emotions : List String := []
  /-- the words that name each emotion (lemmas), by emotion index -/
  lexicon : List (Nat × List String) := []
  appraise : List (AffectRule Nat Nat Nat) := []
  startFeels : List (Nat × Nat × Nat) := []
  pov : Option Nat := none
  /-- (a, c, need): `a` does not register `c`'s need unprompted (`a = c`: one's own) -/
  blind : List (Nat × Nat × Nat) := []
  /-- (character, emotion, n): the character takes the emotion as an anomaly, read as itself after `n` examinations -/
  anomaly : List (Nat × Nat × Nat) := []
  /-- (emotion, need): the emotion is the felt sign of the need -/
  signals : List (Nat × Nat) := []
  /-- (character, tie): the character never starts that kind of tie, only answers one -/
  aloof : List (Nat × Nat) := []
  deriving Repr, DecidableEq

structure XCh (x : XSpec) where i : Nat deriving DecidableEq, Repr
structure XK (x : XSpec) where i : Nat deriving DecidableEq, Repr
structure XR (x : XSpec) where i : Nat deriving DecidableEq, Repr
structure XE (x : XSpec) where i : Nat deriving DecidableEq, Repr

variable {x : XSpec}

instance : TieLaws (XR x) where
  symmetric r := ((x.ties[r.i]?).map (·.symmetric)).getD false
  excludes r := (((x.ties[r.i]?).map (·.excludes)).getD []).map (⟨·⟩)
  requires r := ((x.ties[r.i]?).bind (·.requires)).map fun (r', k) => (⟨r'⟩, k)

instance : CareLaws (XK x) (XR x) where
  consent k := (lookup x.consent k.i).getD .none
  builds := x.builds.map (⟨·⟩)
  threat := x.threat.map (⟨·⟩)
  protects := x.protects.map (⟨·⟩)

instance : TieSight (XCh x) (XR x) where
  aloof c r := x.aloof.contains (c.i, r.i)

instance : CareSight (XCh x) (XK x) where
  blind a c k := x.blind.contains (a.i, c.i, k.i)

instance : AffectReading (XCh x) (XE x) (XK x) where
  anomaly c e := ((x.anomaly.find? fun (c', e', _) => c' == c.i && e' == e.i).map (·.2.2))
  signals e := (lookup x.signals e.i).map (⟨·⟩)

instance : IdentityLaws (XCh x) String String (XR x) where
  pron c := x.pron.getD c.i .they
  names c := (lookup x.names c.i).getD []
  secrets c := (lookup x.secrets c.i).getD []
  trust := x.trust.map (⟨·⟩)

structure XW (x : XSpec) where
  ties : List (Nat × Nat × Nat × Nat) := []
  needs : List (Nat × List (XK x)) := []
  accepted : List (XCh x × XCh x × XK x × Bool) := []
  offers : List (XCh x × XCh x × XK x) := []
  names : List (XCh x × XCh x × String) := []
  pron : List (XCh x × XCh x × Pron) := []
  secrets : List (XCh x × XCh x × String) := []
  harms : List (IdHarm (XCh x) String String) := []
  /-- (character, emotion, level) -/
  affect : List (Nat × Nat × Nat) := []
  registered : List (XCh x × XCh x × XK x × Bool) := []
  examined : List (XCh x × XE x × Nat) := []
  recognised : List (XCh x × XE x) := []
  deriving DecidableEq, Repr

instance : HasTies (XW x) (XCh x) (XR x) where
  tie w r a b := ((w.ties.find? fun (r', a', b', _) => r' == r.i && a' == a.i && b' == b.i).map (·.2.2.2)).getD 0
  setTie w r a b n := { w with ties := (r.i, a.i, b.i, n) ::
    (w.ties.filter fun (r', a', b', _) => !(r' == r.i && a' == a.i && b' == b.i)) }

instance : HasNeeds (XW x) (XCh x) (XK x) where
  needs w c := (lookup w.needs c.i).getD []
  setNeeds w c ks := { w with needs := (c.i, ks) :: w.needs.filter (·.1 != c.i) }
  accepted := XW.accepted
  setAccepted w a := { w with accepted := a }
  offers := XW.offers
  setOffers w o := { w with offers := o }
  registered := XW.registered
  setRegistered w r := { w with registered := r }

instance : HasIdent (XW x) (XCh x) String String where
  knownNames := XW.names
  setKnownNames w n := { w with names := n }
  knownPron := XW.pron
  setKnownPron w p := { w with pron := p }
  knownSecrets := XW.secrets
  setKnownSecrets w s := { w with secrets := s }
  harms := XW.harms
  setHarms w h := { w with harms := h }

instance : HasAffect (XW x) (XCh x) (XE x) where
  feels w c e := ((w.affect.find? fun (c', e', _) => c' == c.i && e' == e.i).map (·.2.2)).getD 0
  setFeels w c e n := { w with affect := (c.i, e.i, n) ::
    (w.affect.filter fun (c', e', _) => !(c' == c.i && e' == e.i)) }
  examined := XW.examined
  setExamined w l := { w with examined := l }
  recognised := XW.recognised
  setRecognised w l := { w with recognised := l }

inductive XEv (x : XSpec) where
  | tie (e : TieEv (XCh x) (XR x))
  | care (e : CareEv (XCh x) (XK x))
  | id (e : IdEv (XCh x) String String)
  | aff (e : AffEv (XCh x) (XE x))
  | read (e : ReadEv (XCh x) (XE x))
  deriving DecidableEq, Repr

def XSpec.rules (x : XSpec) : List (AffectRule (XK x) (XR x) (XE x)) :=
  x.appraise.map fun
    | .onHarm k e d => .onHarm (k.map (⟨·⟩)) ⟨e⟩ d
    | .onTend k e d => .onTend (k.map (⟨·⟩)) ⟨e⟩ d
    | .onShield e d => .onShield ⟨e⟩ d
    | .onTie r e d => .onTie ⟨r⟩ ⟨e⟩ d

/-- A feeling that signals a need is felt only where the need is (`Affect.signOk`). -/
def affSignOk (w : XW x) : AffEv (XCh x) (XE x) → Bool
  | .feel c e => signOk w c e
  | .calm _ _ => true

instance : Domain (XW x) (XEv x) where
  ok w | .tie e => Domain.ok w e | .care e => Domain.ok w e | .id e => Domain.ok w e
       | .aff e => Domain.ok w e && affSignOk w e | .read e => Domain.ok w e
  -- care and ties are appraised: what they make their target feel
  step w
    | .tie e => applyAffect (Domain.step w e) (appraise x.rules (.inr e))
    | .care e => applyAffect (Domain.step w e) (appraise x.rules (.inl e))
    | .id e => Domain.step w e
    | .aff e => Domain.step w e
    | .read e => Domain.step w e
  why w
    | .tie e => Domain.why w e | .care e => Domain.why w e | .id e => Domain.why w e
    | .aff e => if affSignOk w e then Domain.why w e else
        "out of character: this feeling is the felt sign of a need they do not register in themselves " ++
        "(being told they have it is knowing, not feeling)"
    | .read e => Domain.why w e

instance : Perceive (XW x) (XEv x) := Perceive.none

def XSpec.start (x : XSpec) : XW x where
  ties := x.startTies
  needs := (x.startNeeds.map (·.1)).eraseDups.map fun c =>
    (c, (x.startNeeds.filter (·.1 == c)).map fun (_, k) => ⟨k⟩)
  names := x.startNames.map fun (a, b, n) => (⟨a⟩, ⟨b⟩, n)
  pron := x.startPron.map fun (a, b, p) => (⟨a⟩, ⟨b⟩, p)
  secrets := x.startSecrets.map fun (a, b, s) => (⟨a⟩, ⟨b⟩, s)
  affect := x.startFeels

/-! ## References in the text -/

/-- A reference to character `who` at token `at_`: in narration (`speaker =
none`, `narr`), or in a quote whose speaker may be unknown. -/
structure XMention where
  at_ : Nat
  who : Nat
  m : World.Mention String
  narr : Bool
  speaker : Option Nat
  deriving DecidableEq, Repr

def gendered : String → Option Pron
  | "boy" | "boyfriend" | "man" | "guy" | "dude" | "sir" | "gentleman" | "brother" => some .he
  | "girl" | "girlfriend" | "woman" | "lady" | "ma'am" | "gal" | "sister" => some .she
  | _ => none

def pronSeries (form : String) : Option Pron :=
  match form.toLower with
  | "he" | "him" | "his" | "himself" => some .he
  | "she" | "her" | "hers" | "herself" => some .she
  | "they" | "them" | "their" | "theirs" | "themselves" | "themself" => some .they
  | "it" | "its" | "itself" => some .it
  | _ => none

/-- A name as said: without a possessive "'s" and a stutter ("Ch-Chief"). -/
def nameForm (s : String) : String :=
  let s := if s.endsWith "'s" then (s.dropEnd 2).toString else s
  match s.splitOn "-" with
  | [a, b] => if a.length < b.length && (b.toLower.startsWith a.toLower) then b else s
  | _ => s

partial def mentionsIn (chars : List String) (speaker : Option String) (quoted : Bool) (inherit : Option String) :
    Tree → Nat → List XMention × Nat
  | .leaf w, p =>
    let ref := w.ref <|> inherit
    let out : List XMention := match ref.bind (chars.idxOf? ·) with
      | some c =>
        let lem := (w.lemma.getD w.form).toLower
        let m := if w.upos == .PROPN then some (World.Mention.name (nameForm w.form))
          else if w.upos == .PRON then (pronSeries w.form).map .pron
          else if w.upos == .NOUN then (gendered lem).map .pron
          else none
        match m with
        | some m => [{ at_ := p, who := c, m, narr := !quoted,
                       speaker := speaker.bind (chars.idxOf? ·) }]
        | none => []
      | none => []
    (out, p + 1)
  | .node i kids, p =>
    let (speaker, quoted) := if i.cat == .QUOTE then (i.speaker, true) else (speaker, quoted)
    -- a phrase's ref reaches a lone leaf (a pronoun or name NP) only
    let content := kids.filter fun k => match k with | .leaf w => w.upos != .PUNCT | _ => true
    let inh := if content.length == 1 then i.ref <|> inherit else none
    kids.foldl (fun (acc, q) k => let (ms, q') := mentionsIn chars speaker quoted inh k q; (acc ++ ms, q')) ([], p)

def mentionsOf (chars : List String) (d : Doc) : List XMention :=
  (d.sentences.foldl (fun (acc, p) st =>
    let (ms, p') := mentionsIn chars none false none st.tree p
    (acc ++ ms, p')) ([], 0)).1

/-- A word naming an emotion, said of a character (an adjective on a phrase
that refers to them). -/
structure XFeel where
  at_ : Nat
  who : Nat
  emo : Nat
  deriving DecidableEq, Repr

/-- The character a subject refers to: its own ref, or its only content leaf's. -/
partial def subjRef (x : XSpec) : Tree → Option Nat
  | .leaf w => w.ref.bind (x.chars.idxOf? ·)
  | .node i ks => (i.ref.bind (x.chars.idxOf? ·)) <|>
    match ks.filter (fun k => match k with | .leaf w => w.upos != .PUNCT && w.upos != .DET | _ => true) with
    | [k] => subjRef x k
    | _ => none

/-- Feeling words said predicatively ("she was jealous", "I'm mortified"): an
adjective heading a clause whose subject refers to a character, with a copula
(or one contracted into the subject). -/
partial def predFeelsIn (x : XSpec) : Tree → Nat → List XFeel × Nat
  | .leaf _, p => ([], p + 1)
  | .node _ kids, p =>
    let (offs, end_) := kids.foldl (fun (acc, q) k => (acc ++ [q], q + k.render.length)) (([] : List Nat), p)
    let placed := kids.zip offs
    let subj := placed.find? fun (k, _) => match k with
      | .leaf w => w.role == some .nsubj | .node i _ => i.role == some .nsubj
    let cop := kids.any fun k => match k with | .leaf w => w.role == some .cop | _ => false
    let fused := match subj with
      | some (.leaf w, _) => w.form.contains '\'' || w.form.contains '’'
      | _ => false
    let here : List XFeel := match subj.bind (fun (k, _) => subjRef x k) with
      | some c => if !(cop || fused) then [] else placed.filterMap fun (k, o) => match k with
        | .leaf w => if w.upos == .ADJ && w.role == some .head then
            ((x.lexicon.find? fun (_, ws) => ws.contains (w.lemma.getD w.form).toLower).map (·.1)).map
              fun e => { at_ := o, who := c, emo := e }
          else none
        | _ => none
      | none => []
    (here ++ placed.flatMap (fun (k, o) => (predFeelsIn x k o).1), end_)

def predFeelsOf (x : XSpec) (d : Doc) : List XFeel :=
  (d.sentences.foldl (fun (acc, p) st => let (fs, p') := predFeelsIn x st.tree p; (acc ++ fs, p')) ([], 0)).1

/-- The emotion words a document says of characters: attributively ("a frightened
girl", via the completeness facts) or predicatively ("she was jealous"). -/
def feelsOf (s : Spec) (x : XSpec) (d : Doc) : List XFeel :=
  (treeFacts s d).mods.filterMap (fun m => do
    let c ← m.of
    let e ← (x.lexicon.find? fun (_, ws) => ws.contains m.word).map (·.1)
    pure { at_ := m.at_, who := c, emo := e }) ++ predFeelsOf x d

/-- A paragraph of the reading: its events with their tokens, its references
and the feelings it names. -/
structure XPara (x : XSpec) where
  events : List (Nat × XEv x)
  mentions : List XMention
  feels : List XFeel := []
  deriving DecidableEq, Repr

/-- Is reference `m` allowed in state `w`, given the paragraph's events? -/
def mentionOk (x : XSpec) (w : XW x) (evs : List (Nat × XEv x)) (m : XMention) : Bool :=
  let b : XCh x := ⟨m.who⟩
  let referrer := if m.narr then x.pov else m.speaker
  let readAsRefer (p : Pron) : Bool := evs.any fun (at_, e) => at_ == m.at_ && match e with
    | .id (.refer a b' p') => b' == b && p' == p && (m.speaker.map (· == a.i)).getD true
    | _ => false
  match m.m with
  | .name n => match referrer with
    | some a => World.mentionOk (R := XR x) w true ⟨a⟩ b (.name n)
    | none => true
  | .pron p =>
    if m.narr then match referrer with
      | some a => World.mentionOk (R := XR x) w true ⟨a⟩ b (.pron p)
      | none => true
    else p == IdentityLaws.pron String String (R := XR x) b || p == .they || readAsRefer p

/-- A feeling named of `who` is felt then, and read by them as itself (not an anomaly still to explain). -/
def feelOk (w : XW x) (f : XFeel) : Bool :=
  HasAffect.feels w (⟨f.who⟩ : XCh x) (⟨f.emo⟩ : XE x) > 0 && readAs w (⟨f.who⟩ : XCh x) (⟨f.emo⟩ : XE x)

/-- Walk a paragraph: events, references and named feelings in token order (an
event at or before a word's token takes effect first). `none` if an event is
not allowed, or a reference or a feeling is not backed by the state. -/
def XPara.run (p : XPara x) (w : XW x) : Option (XW x) :=
  let rec go (w : XW x) : List (Nat × XEv x) → List XMention → List XFeel → Option (XW x)
    | [], ms, fs => if ms.all (mentionOk x w p.events) && fs.all (feelOk w) then some w else none
    | (a, e) :: es, ms, fs =>
      let (before, after) := ms.partition (·.at_ < a)
      let (fb, fa) := fs.partition (·.at_ < a)
      if !before.all (mentionOk x w p.events) || !fb.all (feelOk w) then none
      else if !Domain.ok w e then none
      else go (Domain.step w e) es after fa
  go w p.events p.mentions p.feels

def runParas (w : XW x) : List (XPara x) → Option (XW x)
  | [] => some w
  | p :: ps => (p.run w).bind (runParas · ps)

/-- The story's reading is allowed throughout, from its opening state. -/
def XValid (x : XSpec) (ps : List (XPara x)) : Bool := (runParas x.start ps).isSome

/-- The harms on record after the story. -/
def harmsAfter (x : XSpec) (ps : List (XPara x)) : List (IdHarm (XCh x) String String) :=
  ((runParas x.start ps).map (·.harms)).getD []

/-! ## Reading the files -/

private def str (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
private def arr (j : Json) (k : String) : List Json :=
  match j.getObjVal? k with | .ok (.arr a) => a.toList | _ => []
private def obj (j : Json) (k : String) : List (String × Json) :=
  match j.getObjVal? k with | .ok (.obj kvs) => kvs.toList | _ => []
private def strsOf (j : Json) : List String := match j with
  | .arr a => a.toList.filterMap (·.getStr?.toOption) | _ => []
private def idxOf (kind : String) (xs : List String) (s : String) : Except String Nat :=
  match xs.idxOf? s with | some i => pure i | none => throw s!"unknown {kind} \"{s}\""

def NameKind.ofString? : String → Option NameKind
  | "given" => some .given | "nick" => some .nick | "family" => some .family
  | "title" => some .title | "coined" => some .coined | "dead" => some .dead | _ => none

def xspecOfJson (s : Spec) (j : Json) : Except String XSpec := do
  let chars := s.chars.map (·.id)
  let e := (j.getObjVal? "ext").toOption.getD (Json.mkObj [])
  let tieIds := (arr e "ties").filterMap (str · "id")
  let needIds := (arr e "needs").filterMap (str · "id")
  let ch := idxOf "character" chars
  let tieOf := idxOf "tie" tieIds
  let ties ← (arr e "ties").mapM fun t => do
    pure ({ id := (str t "id").getD "", symmetric := (t.getObjValAs? Bool "symmetric").toOption.getD false,
            excludes := ← (strsOf ((t.getObjVal? "excludes").toOption.getD (Json.arr #[]))).mapM tieOf,
            requires := ← match (t.getObjVal? "requires").toOption with
              | some (.arr #[r, k]) => do pure (some (← tieOf (r.getStr?.toOption.getD ""), k.getNat?.toOption.getD 0))
              | _ => pure none } : TieSpec)
  let consent := ((arr e "needs").zipIdx).filterMap fun (n, i) =>
    match str n "consent" with
    | some "explicit" => some (i, Consent.explicit) | some "implicit" => some (i, .implicit) | _ => none
  let optTie (k : String) : Except String (Option Nat) := (str e k).mapM tieOf
  let names ← (obj e "names").mapM fun (c, v) => do
    let ns ← (match v with | .arr a => a.toList | _ => []).mapM fun (n : Json) => match n with
      | Json.arr #[nm, k, t] => do
        let some kind := NameKind.ofString? (k.getStr?.toOption.getD "") | throw s!"unknown name kind {k}"
        pure (nm.getStr?.toOption.getD "", kind, t.getNat?.toOption.getD 0)
      | _ => throw "a name is [name, kind, trust]"
    pure (← ch c, ns)
  let secrets ← (obj e "secrets").mapM fun (c, v) => do
    let xs := (match v with | .arr a => a.toList | _ => []).filterMap fun (n : Json) => match n with
      | Json.arr #[x, t] => some (x.getStr?.toOption.getD "", t.getNat?.toOption.getD 0)
      | _ => none
    pure (← ch c, xs)
  let st := (e.getObjVal? "start").toOption.getD (Json.mkObj [])
  let startNeeds ← (obj st "needs").flatMapM fun (c, v) => do
    let c ← ch c
    (strsOf v).mapM fun k => do pure (c, ← idxOf "need" needIds k)
  let quad (j : Json) : Except String (List String) := pure (strsOf j)
  let startTies ← (arr st "ties").mapM fun t => do
    match ← quad t with
    | [a, r, b, n] => pure (← tieOf r, ← ch a, ← ch b, n.toNat?.getD 1)
    | [a, r, b] => pure (← tieOf r, ← ch a, ← ch b, 1)
    | _ => throw "a tie is [a, tie, b, level]"
  let startNames ← (arr st "names").mapM fun t => do
    match ← quad t with
    | [a, b, n] => pure (← ch a, ← ch b, n)
    | _ => throw "a known name is [knower, whose, name]"
  let startPron ← (arr st "pron").mapM fun t => do
    match ← quad t with
    | [a, b, p] => match Pron.ofString? p with
      | some p => pure (← ch a, ← ch b, p)
      | none => throw s!"unknown pronoun {p}"
    | _ => throw "a known pronoun is [knower, whose, pron]"
  let startSecrets ← (arr st "secrets").mapM fun t => do
    match ← quad t with
    | [a, b, x] => pure (← ch a, ← ch b, x)
    | _ => throw "a known secret is [knower, whose, fact]"
  let emotions := (obj e "emotions").map (·.1)
  let emo := idxOf "emotion" emotions
  let lexicon := (obj e "emotions").zipIdx.map fun ((_, v), i) => (i, (strsOf v).map (·.toLower))
  let appraise ← (arr e "appraise").mapM fun r => do
    let int (t : String) : Int := if t.startsWith "-" then -((t.drop 1).toString.toNat?.getD 0 : Int) else (t.toNat?.getD 0 : Int)
    let needOpt (n : String) : Except String (Option Nat) := if n == "any" then pure none else do pure (some (← idxOf "need" needIds n))
    match strsOf r with
    | ["harm", n, em, d] => pure (AffectRule.onHarm (← needOpt n) (← emo em) (int d))
    | ["tend", n, em, d] => pure (AffectRule.onTend (← needOpt n) (← emo em) (int d))
    | ["shield", em, d] => pure (AffectRule.onShield (← emo em) (int d))
    | ["tie", t, em, d] => pure (AffectRule.onTie (← tieOf t) (← emo em) (int d))
    | _ => throw "an appraisal is [harm|tend, need|any, emotion, delta], [shield, emotion, delta] or [tie, tie, emotion, delta]"
  let startFeels ← (arr st "feels").mapM fun t => do
    match strsOf t with
    | [c, em, n] => pure (← ch c, ← emo em, n.toNat?.getD 1)
    | _ => throw "a feeling is [character, emotion, level]"
  -- blind spots: [who, "self" | "others" | character, need]
  let blind ← (arr e "blind").flatMapM fun t => do
    match strsOf t with
    | [a, who, n] => do
      let ai ← ch a
      let k ← idxOf "need" needIds n
      let cs ← match who with
        | "self" => pure [ai]
        | "others" => pure ((List.range chars.length).filter (· != ai))
        | c => do pure [← ch c]
      pure (cs.map fun c => (ai, c, k))
    | _ => throw "a blind spot is [who, self|others|character, need]"
  let anomaly ← (arr e "anomaly").mapM fun t => do
    match strsOf t with
    | [c, em, n] => pure (← ch c, ← emo em, n.toNat?.getD 1)
    | _ => throw "an anomaly is [character, emotion, examinations]"
  let signals ← (obj e "signals").mapM fun (em, v) => do
    pure (← emo em, ← idxOf "need" needIds (v.getStr?.toOption.getD ""))
  let aloof ← (arr e "aloof").mapM fun t => do
    match strsOf t with
    | [c, r] => pure (← ch c, ← tieOf r)
    | _ => throw "an aloof entry is [character, tie]"
  pure { chars, pron := s.chars.map fun c => (Pron.ofString? c.pron).getD .they, blind, anomaly, signals, aloof,
         emotions, lexicon, appraise, startFeels,
         ties, needs := needIds, consent, builds := ← optTie "builds", threat := ← optTie "threat",
         protects := ← optTie "protects", trust := ← optTie "trust", names, secrets,
         startNeeds, startTies, startNames, startPron, startSecrets, pov := s.pov }

def XSpec.ev (x : XSpec) (str : String) : Except String (XEv x) := do
  let ch (c : String) : Except String (XCh x) := do pure ⟨← idxOf "character" x.chars c⟩
  let k (n : String) : Except String (XK x) := do pure ⟨← idxOf "need" x.needs n⟩
  let r (n : String) : Except String (XR x) := do pure ⟨← idxOf "tie" (x.ties.map (·.id)) n⟩
  let p (n : String) : Except String Pron := match Pron.ofString? n with
    | some p => pure p | none => throw s!"unknown pronoun \"{n}\""
  match (str.splitOn " ").filter (· != "") with
  | ["relate", a, t, b] => return .tie (.relate (← ch a) (← r t) (← ch b))
  | ["raise", a, t, b] => return .tie (.raise (← ch a) (← r t) (← ch b))
  | ["lower", a, t, b] => return .tie (.lower (← ch a) (← r t) (← ch b))
  | ["unrelate", a, t, b] => return .tie (.unrelate (← ch a) (← r t) (← ch b))
  | ["harm", a, c, n] => return .care (.harm (← ch a) (← ch c) (← k n))
  | ["offer", a, c, n] => return .care (.offer (← ch a) (← ch c) (← k n))
  | ["accept", c, a, n] => return .care (.accept (← ch c) (← ch a) (← k n))
  | ["acceptQuietly", c, a, n] => return .care (.acceptQuietly (← ch c) (← ch a) (← k n))
  | ["decline", c, a, n] => return .care (.decline (← ch c) (← ch a) (← k n))
  | ["tend", a, c, n] => return .care (.tend (← ch a) (← ch c) (← k n))
  | ["shield", a, c, t] => return .care (.shield (← ch a) (← ch c) (← ch t))
  | ["register", a, c, n] => return .care (.register (← ch a) (← ch c) (← k n))
  | ["point", b, a, c, n] => return .care (.point (← ch b) (← ch a) (← ch c) (← k n))
  | ["seek", c, a, n] => return .care (.seek (← ch c) (← ch a) (← k n))
  | ["introduce", a, b, n] => return .id (.introduce (← ch a) (← ch b) n)
  | ["tellName", a, b, c, n] => return .id (.tellName (← ch a) (← ch b) (← ch c) n)
  | ["learnName", a, b, n] => return .id (.learnName (← ch a) (← ch b) n)
  | ["coin", a, b, n] => return .id (.coin (← ch a) (← ch b) n)
  | ["call", a, b, n] => return .id (.call (← ch a) (← ch b) n)
  | ["assume", a, b, q] => return .id (.assume (← ch a) (← ch b) (← p q))
  | ["learnPron", a, b, q] => return .id (.learnPron (← ch a) (← ch b) (← p q))
  | ["tellPron", a, b, c, q] => return .id (.tellPron (← ch a) (← ch b) (← ch c) (← p q))
  | ["refer", a, b, q] => return .id (.refer (← ch a) (← ch b) (← p q))
  | ["disclose", a, b, s] => return .id (.disclose (← ch a) (← ch b) s)
  | ["out", a, b, s] => return .id (.out (← ch a) (← ch b) s)
  | ["feel", c, e] => return .aff (.feel (← ch c) ⟨← idxOf "emotion" x.emotions e⟩)
  | ["calm", c, e] => return .aff (.calm (← ch c) ⟨← idxOf "emotion" x.emotions e⟩)
  | ["examine", c, e] => return .read (.examine (← ch c) ⟨← idxOf "emotion" x.emotions e⟩)
  | ["recognise", c, e] => return .read (.recognise (← ch c) ⟨← idxOf "emotion" x.emotions e⟩)
  | ["own", c, e] => return .read (.own (← ch c) ⟨← idxOf "emotion" x.emotions e⟩)
  | _ => throw s!"cannot read ext event \"{str}\""

/-- A paragraph's ext reading, from its events file and annotation. -/
def xparaOf (s : Spec) (x : XSpec) (ej : Option Json) (d : Option Doc) : Except String (XPara x) := do
  let evs ← ((ej.map fun j => arr j "ext").getD []).mapM fun it => do
    let some e := str it "e" | throw "ext event without e"
    pure ((it.getObjValAs? Nat "at").toOption.getD 0, ← x.ev e)
  -- stable sort by token, so the walk is in text order
  let evs := sortBy (fun a b => a.1 ≤ b.1) evs
  pure { events := evs, mentions := (d.map (mentionsOf x.chars)).getD [], feels := (d.map (feelsOf s x)).getD [] }

/-! ## The report -/

def XSpec.chS (x : XSpec) (i : Nat) : String := x.chars.getD i s!"?{i}"

def XEv.str (x : XSpec) : XEv x → String
  | .tie e => match e with
    | .relate a r b => s!"relate {x.chS a.i} {(x.ties[r.i]?.map (·.id)).getD "?"} {x.chS b.i}"
    | .raise a r b => s!"raise {x.chS a.i} {(x.ties[r.i]?.map (·.id)).getD "?"} {x.chS b.i}"
    | .lower a r b => s!"lower {x.chS a.i} {(x.ties[r.i]?.map (·.id)).getD "?"} {x.chS b.i}"
    | .unrelate a r b => s!"unrelate {x.chS a.i} {(x.ties[r.i]?.map (·.id)).getD "?"} {x.chS b.i}"
  | .care e => match e with
    | .harm a c k | .offer a c k | .accept a c k | .acceptQuietly a c k | .decline a c k | .tend a c k
    | .register a c k | .seek a c k =>
      s!"{reprStr e |>.splitOn " " |>.headD "" |>.replace "LangLib.World.CareEv." ""} {x.chS a.i} {x.chS c.i} {x.needs.getD k.i "?"}"
    | .shield a c t => s!"shield {x.chS a.i} {x.chS c.i} {x.chS t.i}"
    | .point b a c k => s!"point {x.chS b.i} {x.chS a.i} {x.chS c.i} {x.needs.getD k.i "?"}"
  | .id e => match e with
    | .introduce a b n => s!"introduce {x.chS a.i} {x.chS b.i} '{n}'"
    | .tellName a b c n => s!"tellName {x.chS a.i} {x.chS b.i} {x.chS c.i} '{n}'"
    | .learnName a b n => s!"learnName {x.chS a.i} {x.chS b.i} '{n}'"
    | .coin a b n => s!"coin {x.chS a.i} {x.chS b.i} '{n}'"
    | .call a b n => s!"call {x.chS a.i} {x.chS b.i} '{n}'"
    | .assume a b p => s!"assume {x.chS a.i} {x.chS b.i} {p.name}"
    | .learnPron a b p => s!"learnPron {x.chS a.i} {x.chS b.i} {p.name}"
    | .tellPron a b c p => s!"tellPron {x.chS a.i} {x.chS b.i} {x.chS c.i} {p.name}"
    | .refer a b p => s!"refer {x.chS a.i} {x.chS b.i} {p.name}"
    | .disclose a b s => s!"disclose {x.chS a.i} {x.chS b.i} '{s}'"
    | .out a b s => s!"out {x.chS a.i} {x.chS b.i} '{s}'"
  | .aff (.feel c e) => s!"feel {x.chS c.i} {x.emotions.getD e.i "?"}"
  | .aff (.calm c e) => s!"calm {x.chS c.i} {x.emotions.getD e.i "?"}"
  | .read (.examine c e) => s!"examine {x.chS c.i} {x.emotions.getD e.i "?"}"
  | .read (.recognise c e) => s!"recognise {x.chS c.i} {x.emotions.getD e.i "?"}"
  | .read (.own c e) => s!"own {x.chS c.i} {x.emotions.getD e.i "?"}"

def harmS (x : XSpec) : IdHarm (XCh x) String String → String
  | .misgender a b p d => s!"{x.chS a.i} misgenders {x.chS b.i} ('{p.name}'){if d then ", knowing better" else ", having assumed"}"
  | .deadname a b n => s!"{x.chS a.i} deadnames {x.chS b.i} ('{n}')"
  | .outed a b s => s!"{x.chS a.i} learns {x.chS b.i}'s private fact '{s}' without being told"

def mentionS (x : XSpec) (m : XMention) : String :=
  let what := match m.m with | .name n => s!"the name '{n}'" | .pron p => s!"'{p.name}'"
  let who := if m.narr then s!"the narration ({(x.pov.map x.chS).getD "no point of view"})"
    else s!"{(m.speaker.map x.chS).getD "an unknown speaker"}"
  s!"token {m.at_}: {who} uses {what} for {x.chS m.who}"

/-- Per paragraph: each event's verdict, each reference's, and the state after. -/
def xreport (x : XSpec) (names : List String) (ps : List (XPara x)) : Json := Id.run do
  let mut w := x.start
  let mut out : Array Json := #[]
  let mut ok := true
  for (p, nm) in ps.zip names do
    let mut issues : Array String := #[]
    let mut evJ : Array Json := #[]
    let mut ms := p.mentions
    let mut fs := p.feels
    let feelIssue (w : XW x) (f : XFeel) : String :=
      if HasAffect.feels w (⟨f.who⟩ : XCh x) (⟨f.emo⟩ : XE x) > 0 then
        s!"token {f.at_}: the prose names {x.chS f.who}'s {x.emotions.getD f.emo "?"} as itself, but they still take it as an anomaly to explain: out of character until they recognise it (`examine`, then `recognise`)"
      else s!"token {f.at_}: the prose says {x.chS f.who} feels {x.emotions.getD f.emo "?"}, but nothing has made them (read the event that does: a harm, a threat, or `feel`)"
    for (a, e) in p.events do
      let (fb, fa) := fs.partition (·.at_ < a)
      for f in fb do
        if !feelOk w f then issues := issues.push (feelIssue w f)
      fs := fa
      let (before, after) := ms.partition (·.at_ < a)
      for m in before do
        if !mentionOk x w p.events m then issues := issues.push s!"{mentionS x m}, which they do not know (or, in speech, a misgendering not read as a `refer` event)"
      ms := after
      let good := Domain.ok w e
      evJ := evJ.push (Json.mkObj [("e", XEv.str x e), ("at", a), ("ok", good),
        ("why", if good then "" else Domain.why w e)])
      if !good then issues := issues.push s!"'{XEv.str x e}' (token {a}) cannot happen: {Domain.why w e}"
      w := Domain.step w e
    for f in fs do
      if !feelOk w f then issues := issues.push (feelIssue w f)
    for m in ms do
      if !mentionOk x w p.events m then issues := issues.push s!"{mentionS x m}, which they do not know (or, in speech, a misgendering not read as a `refer` event)"
    if !issues.isEmpty then ok := false
    out := out.push (Json.mkObj [("name", nm), ("events", Json.arr evJ), ("issues", Json.arr (issues.map Json.str)),
      ("mentions", p.mentions.length),
      ("ties", Json.arr (w.ties.filter (·.2.2.2 > 0) |>.map fun (r, a, b, n) =>
        Json.str s!"{x.chS a} {(x.ties[r]?.map (·.id)).getD "?"} {x.chS b} {n}").toArray),
      ("needs", Json.arr (w.needs.map fun (c, ks) =>
        Json.str s!"{x.chS c}: {", ".intercalate (ks.map fun k => x.needs.getD k.i "?")}").toArray),
      ("harms", Json.arr (w.harms.map (Json.str ∘ harmS x)).toArray),
      ("feels", Json.arr (w.affect.filter (·.2.2 > 0) |>.map fun (c, e, n) =>
        Json.str s!"{x.chS c} {x.emotions.getD e "?"} {n}").toArray),
      ("registered", Json.arr (w.registered.map fun (a, c, k, f) =>
        Json.str s!"{x.chS a.i} {if f then "feels" else "has been told of"} {x.chS c.i}'s need: {x.needs.getD k.i "?"}").toArray),
      ("examined", Json.arr (w.examined.map fun (c, e, n) =>
        Json.str s!"{x.chS c.i} {x.emotions.getD e.i "?"} {n}{if readAs w c e then " (recognised)" else ""}").toArray),
      -- who knows what of whom (World/Identity): names, pronouns, private facts
      ("knows", Json.arr ((w.names.map fun ((a, b, n) : XCh x × XCh x × String) => Json.mkObj [("who", x.chS a.i), ("of", x.chS b.i), ("kind", "name"), ("v", n)]) ++
        (w.pron.map fun ((a, b, p) : XCh x × XCh x × Pron) => Json.mkObj [("who", x.chS a.i), ("of", x.chS b.i), ("kind", "pron"), ("v", p.name),
          ("right", p == IdentityLaws.pron String String (R := XR x) b)]) ++
        (w.secrets.map fun ((a, b, s) : XCh x × XCh x × String) => Json.mkObj [("who", x.chS a.i), ("of", x.chS b.i), ("kind", "secret"), ("v", s)])).toArray)])
  return Json.mkObj [("valid", ok && XValid x ps), ("paragraphs", Json.arr out)]

private def readJson (p : System.FilePath) : IO (Option Json) := do
  if ← p.pathExists then
    match Json.parse (← IO.FS.readFile p) with
    | .ok j => pure (some j) | .error _ => pure none
  else pure none

def extInputs (dir : String) : IO (Spec × XSpec × List (String × Option Json × Option Doc)) := do
  let sj ← match Json.parse (← IO.FS.readFile (System.FilePath.mk dir / "story.json")) with
    | .ok j => pure j | .error e => throw (IO.userError e)
  let s ← match specOfJson sj with | .ok s => pure s | .error e => throw (IO.userError e)
  let x ← match xspecOfJson s sj with | .ok x => pure x | .error e => throw (IO.userError e)
  let pdir := System.FilePath.mk dir / "paragraphs"
  let files ← pdir.readDir
  let names := (files.toList.filterMap fun f =>
    if f.fileName.endsWith ".txt" then some (f.fileName.dropEnd 4).toString else none)
  let names := sortBy (fun a b => decide (a ≤ b)) names
  let ps ← names.mapM fun nm => do
    let ej ← readJson (pdir / s!"{nm}.events.json")
    let dj ← if ← (pdir / s!"{nm}.json").pathExists then
        pure (match docOfString (← IO.FS.readFile (pdir / s!"{nm}.json")) with | .ok d => some d | .error _ => none)
      else pure none
    pure (nm, ej, dj)
  pure (s, x, ps)

def extReport (dir : String) : IO Json := do
  let (s, x, ps) ← extInputs dir
  let paras ← ps.mapM fun (_, ej, d) => match xparaOf s x ej d with
    | .ok p => pure p | .error e => throw (IO.userError e)
  pure (xreport x (ps.map (·.1)) paras)

/-- One-line `repr` (a structure instance must not wrap below its first field). -/
private def rs {α : Type} [Repr α] (a : α) : String := (repr a).pretty 1000000

/-- The reading as a Lean file of theorems, each proved by `decide +kernel`. -/
def extLean (dir : String) (ns : String) : IO String := do
  let (s, x, ps) ← extInputs dir
  let paras ← ps.mapM fun (_, ej, d) => match xparaOf s x ej d with
    | .ok p => pure p | .error e => throw (IO.userError e)
  let valid := XValid x paras
  let mut out := s!"import LangLib.Studio.Ext\n\n/-!\n# {ns}: ties, care and identity, generated by `langlib ext --lean`\n\n" ++
    "The `#guard`s fail if the story files no longer match the definitions.\n-/\n\n" ++
    s!"namespace {ns}\nopen LangLib.World LangLib.Studio\n\n" ++
    s!"def xspec : XSpec := {rs x}\n\n" ++
    "#guard xspecMatches (include_str \"story.json\") xspec\n\n"
  for ((nm, ej, d), p) in ps.zip paras do
    out := out ++ s!"def p{nm} : XPara xspec := {rs p}\n" ++
      (if ej.isSome && d.isSome then
        s!"#guard xparaMatches xspec (include_str \"story.json\") (include_str \"paragraphs/{nm}.events.json\") (include_str \"paragraphs/{nm}.json\") p{nm}\n\n"
      else "\n")
  let all := "[" ++ ", ".intercalate (ps.map fun (nm, _, _) => s!"p{nm}") ++ "]"
  out := out ++ s!"def story : List (XPara xspec) := {all}\n\n"
  out := out ++ (if valid then "theorem ext_valid : XValid xspec story = true := by decide +kernel\n"
    else "theorem ext_invalid : XValid xspec story = false := by decide +kernel\n")
  out := out ++ s!"\n/-- Who misgendered, deadnamed or outed whom, and whether they knew better. -/\n" ++
    s!"theorem harms : harmsAfter xspec story = ({rs (harmsAfter x paras)} : List (IdHarm (XCh xspec) String String)) := by decide +kernel\n"
  -- every disclosure the story gates by trust was out of reach at the opening:
  -- it is the care shown in between that makes it allowed
  let gated := (paras.flatMap (·.events)).filterMap fun (_, e) => match e with
    | .id (.introduce a _ n) => if ((nameEntry (X := String) (R := XR x) a n).map (·.2.2)).getD 0 > 0 then some e else none
    | .id (.disclose _ _ _) => some e
    | _ => none
  -- every move the story's personas rule out unprompted (a blind spot, an anomaly not yet read)
  -- was out of reach at the opening: what came between is what makes it in character
  let persona := (paras.flatMap (·.events)).filterMap fun (_, e) => match e with
    | .care (.seek c _ k) | .care (.register c _ k) => if x.blind.contains (c.i, c.i, k.i) then some e else none
    | .care (.offer a c k) | .care (.tend a c k) => if x.blind.contains (a.i, c.i, k.i) then some e else none
    | .read (.recognise c em) | .read (.own c em) => if (x.anomaly.any fun (c', e', _) => c' == c.i && e' == em.i) then some e else none
    | .tie (.relate a r _) | .tie (.raise a r _) => if x.aloof.contains (a.i, r.i) then some e else none
    | _ => none
  for (e, i) in persona.eraseDups.zipIdx do
    out := out ++ s!"\n/-- {XEv.str x e}: out of character at the opening (a blind spot, or a feeling still an anomaly). -/\n" ++
      s!"theorem persona_{i} : Domain.ok xspec.start ({rs e} : XEv xspec) = false := by decide +kernel\n"
  for (e, i) in gated.zipIdx do
    out := out ++ s!"\n/-- {XEv.str x e}: not allowed at the opening, before any trust was earned. -/\n" ++
      s!"theorem gated_{i} : Domain.ok xspec.start ({rs e} : XEv xspec) = false := by decide +kernel\n"
  pure (out ++ s!"\nend {ns}\n")

/-- `story.json` still declares `x`. -/
def xspecMatches (str : String) (x : XSpec) : Bool :=
  match Json.parse str with
  | .ok j => match specOfJson j with
    | .ok s => match xspecOfJson s j with | .ok x' => x' == x | .error _ => false
    | .error _ => false
  | .error _ => false

/-- A paragraph's files still give `p`. -/
def xparaMatches (x : XSpec) (story evs doc : String) (p : XPara x) : Bool :=
  match Json.parse story >>= specOfJson, Json.parse evs, docOfString doc with
  | .ok s, .ok j, .ok d => match xparaOf s x (some j) (some d) with | .ok p' => p' == p | .error _ => false
  | _, _, _ => false

end LangLib.Studio
