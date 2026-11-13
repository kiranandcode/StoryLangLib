import LangLib.Json
import LangLib.Check
import LangLib.World.Lexicon
import LangLib.Studio.Parse
import LangLib.Studio.Refine
import LangLib.Studio.Claim

/-!
# The Studio's per-paragraph report

`langlib story <dir>` reads a story directory and prints one JSON document:
for each paragraph, its checked annotation (tokens, parts of speech,
mentions, quotes, clauses), the events it asserts with the verdict on each,
the state after it, what changed (places, beliefs with explanations, bonds,
consent, goals), the claims it makes about the state and whether they hold,
whether the prose realises the plan, and where its events sit on the solved
timeline. Every verdict is computed by the library's definitions (`Domain.ok3`,
`next`, `view`, `motives`, `Story.solved`); this file only arranges them.

Time: events in the main line follow each other; a `meanwhile` event is at
the same time as the previous main event; `flashback` events precede the
first main event of their paragraph (or the next one), `gap` minutes earlier
when given. Validity is checked in chronological order: the state after
paragraph `k` is the run of every event told so far, in story-time order.
-/

namespace LangLib.Studio
open Lean LangLib LangLib.World LangLib.Scene

inductive Phase | main | meanwhile | flashback
  deriving DecidableEq, Repr

def Phase.name : Phase → String
  | .main => "main" | .meanwhile => "meanwhile" | .flashback => "flashback"

def Phase.ofString : String → Phase
  | "meanwhile" => .meanwhile | "flashback" => .flashback | _ => .main

/-- An event as a paragraph asserts it. -/
structure Item where
  ev : Ev
  /-- where it came from: "plan", "text" (read off the prose), "lexicon" -/
  src : String := "plan"
  /-- token index (in the paragraph) of the words that assert it -/
  at_ : Option Nat := none
  phase : Phase := .main
  /-- for a flashback: minutes before the paragraph's first main event -/
  gap : Option Nat := none
  deriving Repr

instance : Inhabited Item := ⟨{ ev := .move 0 0 }⟩

structure Para where
  name : String
  text : String
  doc : Option Doc := none
  /-- the paragraph's plan, when written top-down -/
  plan : Option (List Ev) := none
  /-- the events the paragraph asserts (read off the prose, or its plan) -/
  items : List Item
  claims : List String := []
  beat : Option String := none
  /-- a reading error (bad event string, unparsable document) -/
  errors : List String := []

/-- How to read facts off complement clauses ("she thought Theo liked her"). -/
structure FactLex where
  verb : String
  subj : Option String := none
  obj : Option String := none
  lit : Fact × Bool

variable {s : Spec}

/-! ## Back from module events to the surface syntax -/

def unlit (l : SFact s × Bool) : Fact × Bool := (l.1.f, l.2)

def Evid.ofCh : Evid (Ch s) → Evid Nat
  | .self => .self | .seen => .seen | .sensed => .sensed | .inferred => .inferred
  | .assumed => .assumed | .told c => .told c.i | .relayed c => .relayed c.i | .rumour => .rumour

def A.toEv : A s → Ev
  | .space (.move c p) => .move c.i p.i | .space (.take c o) => .take c.i o.i
  | .space (.drop c o) => .drop c.i o.i | .space (.give c d o) => .give c.i d.i o.i
  | .mind (.tell c d l) => .tell c.i d.i (unlit l) | .mind (.whisper c d l) => .whisper c.i d.i (unlit l)
  | .mind (.lie c d l) => .lie c.i d.i (unlit l)
  | .mind (.notice c l e) => .notice c.i (unlit l) (Evid.ofCh e)
  | .mind (.realise c l) => .realise c.i (unlit l)
  | .social (.flirt a b) => .flirt a.i b.i | .social (.confide a b) => .confide a.i b.i
  | .social (.argue a b) => .argue a.i b.i | .social (.ask a b x) => .askAct a.i b.i x
  | .social (.agree b a x) => .agree b.i a.i x | .social (.withdraw b a x) => .withdraw b.i a.i x
  | .social (.act a b x) => .act a.i b.i x
  | .dialogue (.ask c d f) => .ask c.i d.i f.f | .dialogue (.answer d c l) => .answer d.i c.i (unlit l)
  | .dialogue (.hint c d l) => .hint c.i d.i (unlit l) | .dialogue (.sarcasm c d l) => .sarcasm c.i d.i (unlit l)
  | .dialogue (.promise c d l) => .promise c.i d.i (unlit l)
  | .dialogue (.request c d l) => .request c.i d.i (unlit l)

/-! ## English glosses -/

def Spec.charName (s : Spec) (i : Nat) : String := (s.chars[i]?.map (·.name)).getD s!"?{i}"

def Spec.factGloss (s : Spec) : Fact → String
  | .at_ c p => s!"{s.charName c} is at the {s.places.getD p "?"}"
  | .objAt o p => s!"the {s.objects.getD o "?"} is in the {s.places.getD p "?"}"
  | .holds c o => s!"{s.charName c} has the {s.objects.getD o "?"}"
  | .did a b x => s!"{s.charName a} and {s.charName b}: {x.name}"
  | .atom i => (s.atoms[i]?.map (·.label)).getD s!"?{i}"

def Spec.litGloss (s : Spec) (l : Fact × Bool) : String :=
  if l.2 then s.factGloss l.1 else s!"not: {s.factGloss l.1}"

def Spec.evGloss (s : Spec) : Ev → String
  | .move c p => s!"{s.charName c} goes to the {s.places.getD p "?"}"
  | .take c o => s!"{s.charName c} takes the {s.objects.getD o "?"}"
  | .drop c o => s!"{s.charName c} puts down the {s.objects.getD o "?"}"
  | .give c d o => s!"{s.charName c} gives {s.charName d} the {s.objects.getD o "?"}"
  | .tell c d l => s!"{s.charName c} tells {s.charName d}: {s.litGloss l}"
  | .whisper c d l => s!"{s.charName c} whispers to {s.charName d}: {s.litGloss l}"
  | .lie c d l => s!"{s.charName c} lies to {s.charName d}: {s.litGloss l}"
  | .notice c l e => s!"{s.charName c} comes to think ({s.names.evidS e}): {s.litGloss l}"
  | .realise c l => s!"{s.charName c} realises: {s.litGloss l}"
  | .flirt a b => s!"{s.charName a} flirts with {s.charName b}"
  | .confide a b => s!"{s.charName a} confides in {s.charName b}"
  | .argue a b => s!"{s.charName a} argues with {s.charName b}"
  | .askAct a b x => s!"{s.charName a} asks {s.charName b} for: {x.name}"
  | .agree b a x => s!"{s.charName b} agrees with {s.charName a} to: {x.name}"
  | .withdraw b a x => s!"{s.charName b} withdraws consent ({x.name}) from {s.charName a}"
  | .act a b x => s!"{s.charName a} and {s.charName b}: {x.name}"
  | .ask c d f => s!"{s.charName c} asks {s.charName d} whether {s.factGloss f}"
  | .answer d c l => s!"{s.charName d} answers {s.charName c}: {s.litGloss l}"
  | .hint c d l => s!"{s.charName c} hints to {s.charName d}: {s.litGloss l}"
  | .sarcasm c d l => s!"{s.charName c}, sarcastic, to {s.charName d}, meaning: {s.litGloss l}"
  | .promise c d l => s!"{s.charName c} promises {s.charName d}: {s.litGloss l}"
  | .request c d l => s!"{s.charName c} asks {s.charName d} to make it so: {s.litGloss l}"
  | .adopt c l => s!"{s.charName c} wants: {s.litGloss l}"
  | .dropGoal c l => s!"{s.charName c} no longer wants: {s.litGloss l}"
  | .intend c p => s!"{s.charName c} plans: {(s.plans[p]?.map (·.id)).getD "?"}"
  | .abandon c l => s!"{s.charName c} gives up on: {s.litGloss l}"

/-! ## Time -/

/-- At the same time as a main event, but taking effect after it. -/
def alongside : List Allen := [.overlappedBy, .contains, .startedBy, .finishedBy, .equal]

/-- The story the paragraphs tell, with what they say about when. -/
def storyOf (ps : List Para) : Story (E s) × List (Nat × Nat) :=
  -- (told index, paragraph index) for every item
  let flat : List (Item × Nat) := (ps.zipIdx).flatMap fun (p, k) => p.items.map (·, k)
  let idxd := flat.zipIdx
  let mains := idxd.filterMap fun ((it, _), i) => if it.phase == .main then some i else none
  let chain (is : List Nat) : List Constraint :=
    (is.zip (is.drop 1)).map fun (i, j) => ⟨i, [.before, .meets], j⟩
  -- a meanwhile segment runs alongside the last main event (taking effect after
  -- it) and the main line resumes after it
  let mw := idxd.filterMap fun ((it, _), i) => if it.phase == .meanwhile then some i else none
  let segments : List (List Nat) := mw.foldl (fun acc i => match acc.getLast? with
    | some seg => if seg.getLast? == some (i - 1) then acc.dropLast ++ [seg ++ [i]] else acc ++ [[i]]
    | none => [[i]]) []
  let together : List Constraint := segments.flatMap fun seg =>
    let first := seg.head!
    let last := seg.getLast!
    let before := (mains.filter (· < first)).getLast?
    let after := mains.find? (· > last)
    chain seg ++
    (before.map fun m => (⟨first, alongside, m⟩ : Constraint)).toList ++
    (after.map fun m => (⟨last, [.before, .meets], m⟩ : Constraint)).toList
  -- flashbacks: grouped by paragraph, chained, before the paragraph's first main event
  let flashCs : List Constraint × List Metric :=
    (List.range ps.length).foldl (fun (cs, ms) k =>
      let fs := idxd.filterMap fun ((it, k'), i) => if k' == k && it.phase == .flashback then some i else none
      let firstMain := (idxd.find? fun ((it, k'), _) => k' == k && it.phase == .main).map (·.2) <|>
        (idxd.find? fun ((it, k'), _) => k' > k && it.phase == .main).map (·.2)
      match fs.getLast?, firstMain with
      | some f, some m =>
        let g := (idxd.find? (·.2 == fs.head!)).bind (·.1.1.gap)
        (cs ++ chain fs ++ [⟨f, [.before, .meets], m⟩],
         ms ++ (g.map fun n => Metric.gap f m (n - n / 6) (n + n / 6)).toList)
      | _, _ => (cs ++ chain fs, ms)) ([], [])
  ({ told := flat.map fun (it, _) => Ev.toE s it.ev,
     constraints := chain mains ++ together ++ flashCs.1,
     metric := flashCs.2 },
   idxd.map fun ((_, k), i) => (i, k))

/-! ## Walking the story -/

structure Step (s : Spec) where
  /-- told index -/
  i : Nat
  status : Tri
  why : String
  before : W s

/-- Run `es` (each with its told index) from `w`, recording each event's status. -/
def walk : W s → List (Nat × E s) → List (Step s) × W s
  | w, [] => ([], w)
  | w, (i, e) :: es =>
    let st : Step s := { i, status := Domain.ok3 w e,
                         why := if Domain.ok3 w e == .yes then "" else Domain.why w e, before := w }
    let (rest, w') := walk (next w e) es
    (st :: rest, w')

/-! ## Snapshots -/

def triName : Tri → String | .yes => "yes" | .no => "no" | .unknown => "unknown"

def Spec.chs (s : Spec) : List (Ch s) := (List.range s.chars.length).map (⟨·⟩)

def litJ (s : Spec) (w : W s) (l : SFact s × Bool) : Json :=
  Json.mkObj [("lit", s.names.litS (unlit l)), ("gloss", s.litGloss (unlit l)),
              ("true", truthLit w l)]

/-- Why `c` holds what they hold about `l.1`, with named evidence. -/
def explainJ (s : Spec) (w : W s) (c : Ch s) (l : SFact s × Bool) : List Json :=
  let v := view w c
  (HasMinds.beliefs w c).filterMap fun h => do
    let l' ← litOf h.b
    if l'.1 != l.1 then none else
    let status :=
      if h.up == .note then "only noted"
      else if v.contains l' then "believed"
      else match v.find? (clash l') with
        | some x => s!"outranked by {s.names.litS (unlit x)}"
        | none => "not believed"
    let src := s.names.evidS (Evid.ofCh h.src)
    return Json.mkObj [("lit", s.names.litS (unlit l')), ("src", src),
      ("reasons", Json.arr (h.reasons.map fun (r, n) => Json.arr #[Json.str r, toJson (n : Int)]).toArray),
      ("strength", toJson ((h.reasons.map (·.2)).sum : Int)), ("attitude", reprStr h.up |>.replace "LangLib.World.Upgrade." ""),
      ("status", status), ("caught", h.caught)]

def placeOf (s : Spec) (w : W s) (c : Ch s) : Json :=
  Json.mkObj [("place", s.places.getD (w.loc c).i "offstage"), ("known", w.known.contains c)]

def objJ (s : Spec) (w : W s) (o : Nat) : Json :=
  match w.holder ⟨o⟩ with
  | some c => Json.mkObj [("heldBy", (s.chars[c.i]?.map (·.id)).getD "?"), ("known", w.objKnown.contains ⟨o⟩)]
  | none => Json.mkObj [("place", s.places.getD (w.objLoc ⟨o⟩).i "?"), ("known", w.objKnown.contains ⟨o⟩)]

def pairs (s : Spec) : List (Ch s × Ch s) :=
  s.chs.flatMap fun a => (s.chs.filter (· != a)).map (a, ·)

def bondsJ (s : Spec) (w : W s) : Json :=
  Json.mkObj ((pairs s).map fun (a, b) =>
    (s!"{s.names.chS a.i}>{s.names.chS b.i}",
     Json.mkObj (dims.map fun d => (d.name, Json.num (HasBonds.bond w a b d)))))

def consentS (s : Spec) : Ch s × Ch s × Act → String
  | (b, a, x) => s!"{s.names.chS b.i} consents to {x.name} with {s.names.chS a.i}"

def goalsS (s : Spec) (w : W s) (c : Ch s) : List String :=
  (goalsOf w c).map fun g => s.names.litS (unlit g)

def plansS (s : Spec) (w : W s) (c : Ch s) : List Json :=
  (w.plans c).map fun p => Json.mkObj [("goal", s.names.litS (unlit p.goal)),
    ("next", Json.arr ((p.steps.map fun a => s.names.evS (A.toEv a)).map Json.str).toArray)]

def stateJ (s : Spec) (w : W s) : Json :=
  Json.mkObj [
    ("at", Json.mkObj (s.chs.map fun c => (s.names.chS c.i, placeOf s w c))),
    ("objects", Json.mkObj ((List.range s.objects.length).map fun o => (s.names.obS o, objJ s w o))),
    ("views", Json.mkObj (s.chs.map fun c =>
      (s.names.chS c.i, Json.arr ((view w c).map (litJ s w)).toArray))),
    ("bonds", bondsJ s w),
    ("consent", Json.arr ((w.consent.map (consentS s)).map Json.str).toArray),
    ("goals", Json.mkObj (s.chs.map fun c => (s.names.chS c.i, Json.arr ((goalsS s w c).map Json.str).toArray))),
    ("plans", Json.mkObj (s.chs.map fun c => (s.names.chS c.i, Json.arr (plansS s w c).toArray))),
    ("promises", Json.arr (w.promises.map fun (c, d, l) => Json.mkObj [
      ("by", s.names.chS c.i), ("to", s.names.chS d.i), ("lit", s.names.litS (unlit l)),
      ("kept", truthLit w l)]).toArray),
    ("questions", Json.arr (w.questions.map fun (c, d, f) => Json.str
      s!"{s.names.chS c.i} asked {s.names.chS d.i}: {s.names.factS f.f}?").toArray)]

/-- What changed between two states. -/
def deltaJ (s : Spec) (w₀ w₁ : W s) : Json :=
  let moves := s.chs.filterMap fun c =>
    if w₀.loc c != w₁.loc c || w₀.known.contains c != w₁.known.contains c then
      some (Json.mkObj [("who", s.names.chS c.i), ("from", s.places.getD (w₀.loc c).i "offstage"),
        ("to", s.places.getD (w₁.loc c).i "offstage"), ("assumed", !w₀.known.contains c && w₁.known.contains c && w₀.loc c == w₁.loc c)])
    else none
  let objs := (List.range s.objects.length).filterMap fun o =>
    if w₀.holder ⟨o⟩ != w₁.holder ⟨o⟩ || w₀.objLoc ⟨o⟩ != w₁.objLoc ⟨o⟩ then
      some (Json.mkObj [("what", s.names.obS o), ("now", objJ s w₁ o)]) else none
  let beliefs := s.chs.flatMap fun c =>
    let v₀ := view w₀ c
    let v₁ := view w₁ c
    let gained := v₁.filter (!v₀.contains ·)
    let lost := v₀.filter (!v₁.contains ·)
    (gained.map fun l => Json.mkObj [("who", s.names.chS c.i), ("change", "gained"),
        ("lit", s.names.litS (unlit l)), ("gloss", s.litGloss (unlit l)),
        ("false", !truthLit w₁ l), ("explain", Json.arr (explainJ s w₁ c l).toArray)]) ++
    (lost.map fun l => Json.mkObj [("who", s.names.chS c.i), ("change", "lost"),
        ("lit", s.names.litS (unlit l)), ("gloss", s.litGloss (unlit l)),
        ("false", !truthLit w₁ l), ("explain", Json.arr (explainJ s w₁ c l).toArray)])
  let nested := (pairs s).flatMap fun (c, d) =>
    let v₀ := viewOf w₀ c d
    ((viewOf w₁ c d).filter (!v₀.contains ·)).map fun l =>
      Json.mkObj [("who", s.names.chS c.i), ("about", s.names.chS d.i),
        ("lit", s.names.litS (unlit l)), ("gloss", s.litGloss (unlit l)),
        ("accurate", (view w₁ d).contains l)]
  let bonds := (pairs s).flatMap fun (a, b) => dims.filterMap fun d =>
    let x := HasBonds.bond w₀ a b d
    let y := HasBonds.bond w₁ a b d
    if x == y then none else
    some (Json.mkObj [("from", s.names.chS a.i), ("to", s.names.chS b.i), ("dim", d.name),
      ("before", Json.num x), ("after", Json.num y)])
  let given := (w₁.consent.filter (!w₀.consent.contains ·)).map (consentS s)
  let withdrawn := (w₀.consent.filter (!w₁.consent.contains ·)).map (consentS s)
  let goals := s.chs.flatMap fun c =>
    let g₀ := goalsS s w₀ c
    ((goalsS s w₁ c).filter (!g₀.contains ·)).map fun g => Json.mkObj [("who", s.names.chS c.i), ("goal", Json.str g)]
  Json.mkObj [("moves", Json.arr moves.toArray), ("objects", Json.arr objs.toArray),
    ("beliefs", Json.arr beliefs.toArray), ("nested", Json.arr nested.toArray),
    ("bonds", Json.arr bonds.toArray),
    ("consentGiven", Json.arr (given.map Json.str).toArray),
    ("consentWithdrawn", Json.arr (withdrawn.map Json.str).toArray),
    ("goals", Json.arr goals.toArray)]

/-! ## The annotation layer -/

private partial def quoteSpans : Tree → Nat → List (Nat × Nat × String) × Nat
  | .leaf _, p => ([], p + 1)
  | t@(.node i kids), p =>
    let here := if i.cat == .QUOTE then [(p, p + t.render.length, i.speaker.getD "")] else []
    let (inner, stop) := kids.foldl (fun (acc, q) k => let (xs, q') := quoteSpans k q; (acc ++ xs, q')) ([], p)
    (here ++ inner, stop)

def timeWords : List String :=
  ["meanwhile", "while", "earlier", "later", "before", "after", "ago", "then", "now", "once",
   "already", "still", "until", "when", "soon", "tonight", "midnight", "evening", "morning",
   "hour", "hours", "minute", "minutes", "o'clock", "eleven", "ten", "twelve", "nine", "late",
   "yesterday", "tomorrow", "previously", "simultaneously", "finally", "again"]

def docJ (text : String) (d : Doc) : Json :=
  let r := check text d
  let leaves := d.sentences.flatMap (·.tree.leaves)
  let ms := d.mentions
  let refs := r.refs.pronouns
  let mentionAt (i : Nat) : Option (Mention × String) :=
    (ms.filter fun m => m.pos ≤ i && i < m.pos + (m.text.splitOn " ").length).getLast?.map fun m =>
      (m, ((refs.find? fun (m', _) => m'.pos == m.pos).map (·.2.name)).getD (if m.kind == .full then "full" else ""))
  let quotes := (d.sentences.foldl (fun (acc, p) s => let (xs, p') := quoteSpans s.tree p; (acc ++ xs, p')) ([], 0)).1
  let clauses := d.clauses
  let toks := leaves.zipIdx.map fun (w, i) =>
    let base : List (String × Json) := [("w", w.form), ("p", w.upos.name)]
    let ment := match mentionAt i with
      | some (m, ph) => [("ent", Json.str m.entity), ("mk", Json.str (if m.kind == .pronoun then "pron" else "name")),
                         ("phora", Json.str ph), ("mstart", Json.bool (m.pos == i))]
      | none => []
    let q := match quotes.find? fun (a, b, _) => a ≤ i && i < b with
      | some (_, _, spk) => [("spk", Json.str (if spk == "" then "?" else spk))]
      | none => []
    let verb := if clauses.any (·.at_ == i) then [("clause", Json.bool true)] else []
    let tw := if timeWords.contains w.form.toLower then [("time", Json.bool true)] else []
    Json.mkObj (base ++ ment ++ q ++ verb ++ tw)
  Json.mkObj [("check", r.toJson text), ("tokens", Json.arr toks.toArray),
    ("entities", Json.arr (d.entities.map fun e => Json.mkObj [("id", e.id), ("name", e.name),
      ("kind", e.kind.name)]).toArray),
    ("clauses", Json.arr (clauses.map fun c => Json.mkObj [("verb", c.verb), ("at", c.at_),
      ("subj", c.subj.getD ""), ("obj", c.obj.getD ""), ("embedded", c.embedded),
      ("advs", Json.arr (c.advs.map Json.str).toArray)]).toArray)]

/-! ## Reading events off the checked prose -/

def resolverOf (s : Spec) (d : Doc) : Resolver (Ch s) (Pl s) (Ob s) :=
  let nameOf (e : EntityId) : String :=
    ((d.entities.find? (·.id == e)).map (·.name.toLower)).getD e.toLower
  let find (ids : List String) (names : List String) (e : EntityId) : Option Nat :=
    ids.idxOf? e.toLower <|> ids.idxOf? (nameOf e) <|>
    names.idxOf? (nameOf e) <|>
    (ids.findIdx? fun i => (nameOf e).endsWith i)
  { char := fun e => (find (s.chars.map (·.id.toLower)) (s.chars.map (·.name.toLower)) e).map (⟨·⟩)
    place := fun e => (find s.places s.places e).map (⟨·⟩)
    obj := fun e => (find s.objects s.objects e).map (⟨·⟩) }

def factOfLex (s : Spec) (R : Resolver (Ch s) (Pl s) (Ob s)) (lex : List FactLex)
    (c : Clause) : Option (SFact s × Bool) :=
  (lex.find? fun f => f.verb == c.verb &&
    (f.subj.all fun x => (c.subj.bind R.char).map (s.names.chS ·.i) == some x) &&
    (f.obj.all fun x => (c.obj.bind R.char).map (s.names.chS ·.i) == some x)).map (lit ·.lit)

def lexEvents (s : Spec) (lex : List FactLex) (d : Doc) : List (Clause × Ev) :=
  let R := resolverOf s d
  let f := factOfLex s R lex
  let L : Lexicon (A s) := (spaceLex R).inj ++ (socialLex R).inj ++ (mindLex R f).inj ++ (dialogueLex R f).inj
  (L.events d).map fun (c, a) => (c, A.toEv a)

/-! ## The report -/

def countDiff {α : Type} [BEq α] (xs ys : List α) : List α :=
  ys.foldl (fun acc y => acc.erase y) xs

def report (s : Spec) (B : Option Beats) (beatStory : List String) (lex : List FactLex)
    (ps : List Para) : Json := Id.run do
  let n := s.names
  let (story, owner) := storyOf (s := s) ps
  let timed := story.solved
  let timeOk : Bool := match timed with
    | some t => decide (t.timeline.Satisfies story.constraints) && story.metric.all (·.sat t.timeline)
    | none => false
  let order : List Nat := match timed with
    | some t => if timeOk then t.timeline.byEffect else List.range story.told.length
    | none => List.range story.told.length
  let paraOf (i : Nat) : Nat := ((owner.find? (·.1 == i)).map (·.2)).getD 0
  let start := s.start
  let mut prev := start
  let mut out : Array Json := #[]
  let mut storyline : Array Json := #[]
  -- told index of each paragraph's first item
  let offsets := (ps.foldl (fun (acc, o) p => (acc ++ [o], o + p.items.length)) ([], 0)).1
  for ((p : Para), (k : Nat)) in ps.zipIdx do
    let seq := (order.filter fun i => paraOf i ≤ k).filterMap fun i => (story.told[i]?).map (i, ·)
    let (steps, w) : List (Step s) × W s := walk start seq
    let off := offsets.getD k 0
    let mine := steps.filter fun st => paraOf st.i == k
    let earlierChanged := steps.filter fun st => paraOf st.i < k && st.status != .yes
    let mot := motives (S := E s) (E := A s) start (seq.map (·.2)) 0
    let unmot := (mot.filterMap fun (j, m) => match m with
      | .none _ => (seq[j]?).map (·.1) | _ => none)
    let evs := p.items.zipIdx.map fun ((it : Item), (j : Nat)) =>
      let i := off + j
      let st := mine.find? fun (st : Step s) => st.i == i
      let iv := timed.bind fun t => t.timeline[i]?
      Json.mkObj [("e", n.evS it.ev), ("gloss", s.evGloss it.ev), ("src", it.src),
        ("at", match it.at_ with | some a => Json.num a | none => Json.null),
        ("phase", it.phase.name), ("parties", Json.arr ((it.ev.parties.map n.chS).map Json.str).toArray),
        ("status", triName ((st.map fun (x : Step s) => x.status).getD .unknown)),
        ("why", (st.map fun (x : Step s) => x.why).getD ""),
        ("unmotivated", unmot.contains i),
        ("motive", match (mot.find? fun (jm : Nat × Motive (Ch s) (SFact s)) => (seq[jm.1]?).map (fun (x : Nat × E s) => x.1) == some i) with
          | some (_, .step c g) => s!"{n.chS c.i}'s plan for {n.litS (unlit g)}"
          | some (_, .goal c g) => s!"{n.chS c.i} wants {n.litS (unlit g)}"
          | some (_, .none c) => s!"no goal or plan of {n.chS c.i}"
          | none => ""),
        ("time", match iv with | some v => Json.arr #[Json.num v.s, Json.num v.e] | none => Json.null)]
    let anyNo := mine.any fun (x : Step s) => x.status == .no
    let anyUnknown := mine.any fun (x : Step s) => x.status == .unknown
    let verdict := if anyNo then "failing" else if anyUnknown then "plausible" else "valid"
    let claims := p.claims.map fun c => match n.claim c with
      | .ok cl => Json.mkObj [("claim", c), ("holds", cl.eval w)]
      | .error e => Json.mkObj [("claim", c), ("holds", false), ("error", e)]
    let real := match p.plan with
      | some plan =>
        let got := p.items.map fun (it : Item) => it.ev
        Json.mkObj [("planned", Json.arr ((plan.map n.evS).map Json.str).toArray),
          ("missing", Json.arr (((countDiff plan got).map n.evS).map Json.str).toArray),
          ("extra", Json.arr (((countDiff got plan).map n.evS).map Json.str).toArray),
          ("realises", decide (Refines some got plan))]
      | none => Json.null
    let (docj, lexj) := match p.doc with
      | some d =>
        let le := lexEvents s lex d
        let got := p.items.map fun (it : Item) => it.ev
        (docJ p.text d, Json.arr (le.map fun ((c : Clause), (e : Ev)) => Json.mkObj [("at", c.at_), ("verb", c.verb),
          ("e", n.evS e), ("asserted", got.contains e)]).toArray)
      | none => (Json.null, Json.arr #[])
    out := out.push (Json.mkObj [
      ("name", p.name), ("text", p.text), ("beat", match p.beat with | some b => Json.str b | none => Json.null),
      ("errors", Json.arr (p.errors.map Json.str).toArray),
      ("doc", docj), ("lexicon", lexj),
      ("events", Json.arr evs.toArray), ("verdict", verdict),
      ("assumptions", Json.arr ((mine.filter fun (x : Step s) => x.status == .unknown).map fun (st : Step s) =>
        Json.mkObj [("e", ((story.told[st.i]?).map fun _ => n.evS (((ps.flatMap fun (q : Para) => q.items)[st.i]!).ev)).getD ""),
                    ("why", st.why)]).toArray),
      ("retro", Json.arr (earlierChanged.map fun (st : Step s) => Json.mkObj [("i", st.i), ("status", triName st.status),
        ("why", st.why)]).toArray),
      ("claims", Json.arr claims.toArray), ("realisation", real),
      ("delta", deltaJ s prev w), ("state", stateJ s w)])
    storyline := storyline.push (Json.mkObj (s.chs.map fun c => (n.chS c.i, placeOf s w c)))
    prev := w
  -- beats
  let beatsJ : Json := match B with
    | none => Json.null
    | some B =>
      let ids := B.vocab.map (·.id)
      let coarse : List (BeatEv B) := beatStory.filterMap fun b => (ids.idxOf? b).map (⟨·⟩)
      let fine := ps.flatMap fun p => (p.plan.getD (p.items.map (·.ev)))
      let absd := fine.filterMap B.abs
      let firstBad := firstFailure B.start coarse 0
      Json.mkObj [
        ("conds", Json.arr (B.conds.map Json.str).toArray),
        ("vocab", Json.arr (B.vocab.map fun b => Json.mkObj [("id", b.id), ("label", b.label),
          ("pre", Json.arr ((b.pre.map (B.conds.getD · "?")).map Json.str).toArray),
          ("add", Json.arr ((b.add.map (B.conds.getD · "?")).map Json.str).toArray),
          ("keys", Json.arr ((b.keys.map n.evS).map Json.str).toArray)]).toArray),
        ("story", Json.arr (beatStory.map Json.str).toArray),
        ("valid", decide (Valid B.start coarse)),
        ("failure", match firstBad with | some (i, why) => Json.mkObj [("i", i), ("why", why)] | none => Json.null),
        ("abstracted", Json.arr (absd.map fun b => Json.str (B.beat b.i).id).toArray),
        ("refines", decide (Refines B.abs fine coarse))]
  let all := (ps.flatMap (·.items)).map fun it => Ev.toE s it.ev
  let chrono := order.filterMap (story.told[·]?)
  return Json.mkObj [
    ("characters", Json.arr (s.chars.map fun c => Json.mkObj [("id", c.id), ("name", c.name), ("pron", c.pron),
      ("traits", Json.arr ((c.traits.map fun t => (reprStr t).replace "LangLib.World.Trait." "").map Json.str).toArray),
      ("values", Json.arr ((c.values.map fun t => (reprStr t).replace "LangLib.World.Value." "").map Json.str).toArray)]).toArray),
    ("places", Json.arr (s.places.map Json.str).toArray),
    ("objects", Json.arr (s.objects.map Json.str).toArray),
    ("atoms", Json.arr (s.atoms.map fun a => Json.mkObj [("id", a.id), ("label", a.label), ("truth", a.truth)]).toArray),
    ("start", stateJ s start),
    ("startLine", Json.mkObj (s.chs.map fun c => (n.chS c.i, placeOf s start c))),
    ("storyline", Json.arr storyline),
    ("paragraphs", Json.arr out),
    ("time", Json.mkObj [("consistent", timeOk), ("toldOrder", decide (chrono = all)),
      ("constraints", story.constraints.length)]),
    ("verdict", Json.mkObj [
      ("valid", validB start chrono), ("plausible", plausibleB start chrono),
      ("assumptions", (assumptions start chrono 0).length),
      ("failure", match firstFailure start chrono 0 with
        | some (i, why) => Json.mkObj [("i", i), ("why", why)] | none => Json.null)]),
    ("beats", beatsJ)]

end LangLib.Studio
