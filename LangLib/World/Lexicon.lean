import LangLib.Story.Bridge
import LangLib.World.Mind
import LangLib.World.Social
import LangLib.World.Magic
import LangLib.World.Dialogue

/-!
# Verb lexicons: from checked text to a told story

A lexicon maps a clause (a verb with its subject, object, obliques and
complement, read off a checked langlib document by `Doc.clauses`) to a module's
event. Each module has one; a story composes the ones it uses, exactly as it
composes the modules (`Lexicon.inj`, `++`).

`Lexicon.story` turns a document into a `Story`: its events in the order the
text tells them, and what the text says about when, from the clauses'
adverbials:
* plain narration: each event before (or meeting) the next;
* "meanwhile", "while": at the same time as the previous event of the main line;
* "earlier", "before", "ago": a flashback, before the first event of the main
  line; with an amount ("an hour earlier") also a duration constraint.

Time is in minutes. The timeline itself comes from the solver (`Story.solved`)
and is re-checked by `Timed.Valid`.
-/

namespace LangLib.World
open LangLib LangLib.Scene

structure Lexicon (E : Type) where
  /-- verbs (lemmas) an entry covers, and how a clause becomes an event; the
  second argument is every clause of the document, for complements -/
  entries : List (List String × (Clause → List Clause → Option E))

instance {E : Type} : Append (Lexicon E) := ⟨fun a b => ⟨a.entries ++ b.entries⟩⟩

def Lexicon.map {E E' : Type} (f : E → E') (L : Lexicon E) : Lexicon E' :=
  ⟨L.entries.map fun (vs, g) => (vs, fun c cs => (g c cs).map f)⟩

/-- Put a module's lexicon into the story's event sum. -/
def Lexicon.inj {E S : Type} [Inject E S] (L : Lexicon E) : Lexicon S := L.map ev

def Lexicon.read {E : Type} (L : Lexicon E) (c : Clause) (cs : List Clause) : Option E :=
  L.entries.findSome? fun (vs, g) => if vs.contains c.verb then g c cs else none

/-- Events of a document, each with its clause; complements are not events. -/
def Lexicon.events {E : Type} (L : Lexicon E) (d : Doc) : List (Clause × E) :=
  let cs := d.clauses
  cs.filterMap fun c => if c.embedded then none else (L.read c cs).map (c, ·)

def _root_.LangLib.Scene.Clause.oblTo (c : Clause) (preps : List String) : Option EntityId :=
  (c.obls.find? fun (p, _) => preps.contains p).map (·.2)

def _root_.LangLib.Scene.Clause.complement (c : Clause) (cs : List Clause) : Option Clause :=
  c.comp.bind fun a => cs.find? (·.at_ == a)

variable {C P O : Type}

def spaceLex (R : Resolver C P O) : Lexicon (SpaceEv C P O) := ⟨[
  (["go", "walk", "run", "slip", "creep", "return", "climb", "head", "come", "hurry"],
    fun c _ => do
      return .move (← c.subj >>= R.char)
        (← c.oblTo ["to", "into", "toward", "towards", "onto", "up"] >>= R.place)),
  (["take", "grab", "pick", "snatch", "steal", "pocket"],
    fun c _ => do return .take (← c.subj >>= R.char) (← c.obj >>= R.obj)),
  (["leave", "drop", "put", "set", "hide"],
    fun c _ => do return .drop (← c.subj >>= R.char) (← c.obj >>= R.obj)),
  (["give", "hand", "pass"],
    fun c _ => do
      return .give (← c.subj >>= R.char) (← c.oblTo ["to"] >>= R.char) (← c.obj >>= R.obj))]⟩

/-- Which kind of intimacy a word names. -/
def actOf : String → Option Act
  | "kiss" => some .kiss | "touch" | "caress" => some .touch
  | "undress" => some .undress | "hold" | "hand" | "hands" => some .holdHands
  | "sex" | "sleep" => some .sex
  | _ => none

def socialLex (R : Resolver C P O) : Lexicon (SocialEv C) := ⟨[
  (["flirt"], fun c _ => do return .flirt (← c.subj >>= R.char) (← c.oblTo ["with"] >>= R.char)),
  (["confide", "open"],
    fun c _ => do return .confide (← c.subj >>= R.char) (← c.oblTo ["in", "to"] >>= R.char)),
  (["argue", "quarrel", "fight"],
    fun c _ => do return .argue (← c.subj >>= R.char) (← c.oblTo ["with"] >>= R.char)),
  (["ask", "beg"], fun c cs => do
    let x ← (c.oblNouns.findSome? fun (p, n) => if p == "for" then actOf n else none) <|>
            ((c.complement cs).bind fun k => actOf k.verb)
    return .ask (← c.subj >>= R.char) (← c.obj >>= R.char) x),
  (["agree", "consent"], fun c cs => do
    let k ← c.complement cs
    return .agree (← c.subj >>= R.char) (← ((k.obj <|> k.oblTo ["with"]) >>= R.char)) (← actOf k.verb)),
  (["kiss", "touch", "caress", "undress", "hold"], fun c _ => do
    return .act (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["with"]) >>= R.char)) (← actOf c.verb)),
  (["sleep"], fun c _ => do
    return .act (← c.subj >>= R.char) (← c.oblTo ["with"] >>= R.char) .sex)]⟩

/-- Telling, whispering and lying: what is said comes from the complement
clause, which `factOf` reads as a literal. -/
def mindLex {Φ : Type} (R : Resolver C P O) (factOf : Clause → Option (Φ × Bool)) :
    Lexicon (MindEv C Φ) := ⟨[
  (["tell", "say", "admit", "explain", "claim", "swear", "insist", "confess"], fun c cs => do
    return .tell (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← (c.complement cs).bind factOf)),
  (["whisper"], fun c cs => do
    return .whisper (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← (c.complement cs).bind factOf)),
  (["lie"], fun c cs => do
    return .lie (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← (c.complement cs).bind factOf)),
  -- evidentials: how the subject came to believe the complement
  (["see", "watch", "spot"], fun c cs => do
    return .notice (← c.subj >>= R.char) (← (c.complement cs).bind factOf) .seen),
  (["hear", "feel", "smell"], fun c cs => do
    return .notice (← c.subj >>= R.char) (← (c.complement cs).bind factOf) .rumour),
  (["guess", "suppose", "assume", "suspect"], fun c cs => do
    return .notice (← c.subj >>= R.char) (← (c.complement cs).bind factOf) .assumed),
  -- factive: the narrator commits to the complement, and the subject must be able to know it
  (["realise", "realize", "know", "discover", "understand"], fun c cs => do
    return .realise (← c.subj >>= R.char) (← (c.complement cs).bind factOf))]⟩

/-- Questions, answers, hints, sarcasm, promises and requests. The content comes
from the complement clause; for `ask` only the fact matters (whether ...). -/
def dialogueLex {Φ : Type} (R : Resolver C P O) (factOf : Clause → Option (Φ × Bool)) :
    Lexicon (DialogueEv C Φ) := ⟨[
  (["ask", "wonder", "inquire"], fun c cs => do
    let k ← c.complement cs
    if k.verb == "kiss" || (actOf k.verb).isSome then none else
    return .ask (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← factOf k).1),
  (["answer", "reply", "respond"], fun c cs => do
    return .answer (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← (c.complement cs).bind factOf)),
  (["hint", "imply", "suggest"], fun c cs => do
    return .hint (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← (c.complement cs).bind factOf)),
  (["tease", "joke", "mock"], fun c cs => do
    return .sarcasm (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to", "with"]) >>= R.char)) (← (c.complement cs).bind factOf)),
  (["promise", "vow", "pledge"], fun c cs => do
    return .promise (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← (c.complement cs).bind factOf)),
  (["request", "beg", "urge"], fun c cs => do
    return .request (← c.subj >>= R.char) (← ((c.obj <|> c.oblTo ["to"]) >>= R.char)) (← (c.complement cs).bind factOf))]⟩

def spellOf : String → Option Spell
  | "light" => some .light | "ward" => some .ward | "heal" => some .heal
  | "glamour" => some .glamour | _ => none

def magicLex (R : Resolver C P O) : Lexicon (MagicEv C) := ⟨[
  (["cast"], fun c _ => do
    let s ← c.objNoun.bind spellOf
    let caster ← c.subj >>= R.char
    return .cast caster s ((c.oblTo ["on", "at", "over"] >>= R.char).getD caster)),
  (["ward", "heal"], fun c _ => do
    let caster ← c.subj >>= R.char
    return .cast caster (← spellOf c.verb) ((c.obj >>= R.char).getD caster)),
  (["rest", "sleep"], fun c _ => do
    if (c.oblTo ["with"]).isSome then none else return .rest (← c.subj >>= R.char))]⟩

/-! ## Time from adverbials -/

inductive Phase | main | meanwhile | flashback
  deriving DecidableEq, Repr

def _root_.LangLib.Scene.Clause.phase (c : Clause) : Phase :=
  if c.advs.any (["meanwhile", "while", "simultaneously"].contains ·) then .meanwhile
  else if c.advs.any (["earlier", "before", "ago", "previously"].contains ·) then .flashback
  else .main

private def count : String → Option Nat
  | "a" | "an" | "one" => some 1 | "two" => some 2 | "three" => some 3 | "few" => some 3
  | "five" => some 5 | "ten" => some 10 | "twenty" => some 20 | "half" => some 0
  | s => s.toNat?

private def unit : String → Option Nat
  | "minute" | "minutes" => some 1 | "hour" | "hours" => some 60
  | "day" | "days" => some 1440 | _ => none

/-- Minutes named by an adverbial ("an hour earlier" ↦ 60). -/
def _root_.LangLib.Scene.Clause.amount (c : Clause) : Option Nat :=
  let ws := c.advs
  (ws.zip (ws.drop 1)).findSome? fun (n, u) => do return (← count n) * (← unit u)

def sameTime : List Allen :=
  [.during, .overlaps, .overlappedBy, .contains, .starts, .startedBy, .finishes, .finishedBy, .equal]

/-- The story the document tells, with what its adverbials say about when. -/
def Lexicon.story {E : Type} (L : Lexicon E) (d : Doc) : Story E :=
  let evs := (L.events d).zipIdx
  let idx (ph : Phase) := evs.filterMap fun ((c, _), i) => if c.phase == ph then some i else none
  let chain (is : List Nat) : List Constraint :=
    (is.zip (is.drop 1)).map fun (i, j) => ⟨i, [.before, .meets], j⟩
  let mains := idx .main
  let flashes := idx .flashback
  let together : List Constraint := (idx .meanwhile).filterMap fun i =>
    ((mains.filter (· < i)).getLast? <|> mains.head?).map fun m => ⟨i, sameTime, m⟩
  let flash : List Constraint := match flashes.getLast?, mains.head? with
    | some f, some m => [⟨f, [.before, .meets], m⟩]
    | _, _ => []
  let metric : List Metric := match flashes.head?, mains.head? with
    | some f, some m =>
      match evs[f]?.bind fun ((c, _), _) => c.amount with
      | some n => [.gap f m (n - n / 6) (n + n / 6)]
      | none => []
    | _, _ => []
  { told := evs.map (·.1.2),
    constraints := chain mains ++ chain flashes ++ flash ++ together,
    metric }

end LangLib.World
