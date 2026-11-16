import LangLib.World.Mind

/-!
# The Death Note (the power system of *Death Note*)

A third story-specific power system, in the style of `Nen.lean`. Nen turns on
resources (aura, hands, a book); the Death Note turns on knowledge. Its one
move is writing a name, and whether a write kills depends on what the writer
knows: a face they have seen, and a name that is really the person's.

* **Names and faces.** Every character has one real name (`realName`) and may
  go by aliases. A character knows the faces they have seen (`faces`: in
  person, on a screen, in a photo) and the names they have heard for each
  person (`names`), which may be false. Only the real name, written while
  picturing that person's face, takes. A homonym is not affected: the face
  picked the person, and someone else with the same name was not pictured.
* **Entries.** `write c n x` is `c` writing the name `n` while picturing `x`;
  `c` can only write a name they have heard for `x`. Whether it takes is decided
  when it is written (`nameWhy`) and frozen in the entry, with the reason when
  it does not (`Refusal`), so a story can show why a write did nothing. Nothing
  in the module tells a writer whether a name is real except writing it and
  waiting.
* **Cause, details, time.** With no cause written within 40 seconds of the
  name, the victim dies of a heart attack at 40 seconds. A cause written in time
  opens a window of 6 minutes 40 seconds for the details (the victim's actions
  before death, and the time of death, in seconds after the details). A cause
  must be physically possible for the victim and must not directly kill anyone
  else; the actions must be within what the victim could do, kill nobody else,
  and fit in 23 days. Details that fail are refused with their reason; the death
  still comes (a refused cause is a heart attack at 40 seconds; refused details
  leave the cause to play out when the window closes).
* **Time.** `pass d` advances the clock by `d` seconds; every victim whose
  death falls due by then dies. `died x` and `lives x` are narration checks.
* **Control.** `act x a`: the victim does what was written, only while it was
  written and before their death.
* **Pages and the shinigami.** The owner holds the note; a page or a scrap of it
  works as well (`holds`). Whoever has touched the note or a page can see its
  shinigami (`seeShinigami`, a narration check).
* **The eye deal.** The owner can trade half their remaining life for eyes that
  show the real name of every face they see (`eyeDeal`).

Every refused move says why, in words (`Refusal.text`).
-/

namespace LangLib.World

/-- A cause of death, as data: whom it is possible for, and whom else it would kill. -/
structure CauseDef (C : Type) where
  name : String
  possible : C → Bool := fun _ => true
  harms : List C := []

/-- An action the victim can be made to take before death: who could do it, and whom it would kill. -/
structure ActDef (C : Type) where
  name : String
  able : C → Bool := fun _ => true
  harms : List C := []

/-- How a face is seen. -/
inductive Sight | inPerson | screen | photo
  deriving DecidableEq, Repr

/-- Why a move of the note did nothing, or could not be made. Codes, not words,
so states compare cheaply; `Refusal.text` gives the words. -/
inductive Refusal (C N K A : Type) where
  | dead (c : C)
  | noPage (c : C)
  | unheard (c : C) (n : N) (x : C)
  | noFace (c x : C)
  /-- `n` is not `x`'s real name; `homonym`: whose name it is, if anyone's -/
  | fakeName (n : N) (x : C) (homonym : Option C)
  | victimDead (x : C)
  | alreadyWritten (x : C)
  | noEntry
  | tooLateCause
  | causeImpossible (k : K) (x : C)
  | causeHarms (k : K) (y : C)
  | tooLateDetails
  | noCause
  | cannotDo (a : A) (x : C)
  | actHarms (a : A) (y : C)
  | tooLong
  | notWritten (x : C) (a : A)
  | alreadyDone (x : C) (a : A)
  | alive (x : C)
  | notOwner (c : C)
  | untouched (c : C)
  | hasEyes (c : C)
  | apart (c x : C)
  /-- the cause or details written for the victim were refused, for this reason -/
  | refused (r : Refusal C N K A)
  deriving DecidableEq, Repr

/-- An entry in the note. Its verdicts are taken when each part is written. -/
structure Entry (C N K A : Type) where
  writer : C
  name : N
  face : C
  /-- second the name was written -/
  t0 : Nat
  /-- why the name does not take (none: it does) -/
  void : Option (Refusal C N K A) := none
  cause : Option K := none
  causeAt : Nat := 0
  /-- why the cause was refused (none: it stands) -/
  causeVoid : Option (Refusal C N K A) := none
  acts : List A := []
  detailsAt : Option Nat := none
  /-- the time of death the details set (absolute seconds) -/
  dieAt : Option Nat := none
  detailsVoid : Option (Refusal C N K A) := none
  deriving DecidableEq, Repr

structure NoteState (C N K A : Type) where
  realName : C → N
  /-- names and people as the text says them -/
  label : C → String
  spell : N → String
  causes : K → CauseDef C
  actDefs : A → ActDef C
  /-- current story time, in seconds -/
  now : Nat := 0
  alive : C → Bool := fun _ => true
  /-- when each person died (seconds), and of what (none: a heart attack) -/
  deathAt : C → Option (Nat × Option K) := fun _ => none
  owner : Option C := none
  /-- holds the note or a page of it -/
  holds : C → Bool := fun _ => false
  touched : C → Bool := fun _ => false
  eyes : C → Bool := fun _ => false
  /-- remaining life, in days -/
  life : C → Nat := fun _ => 0
  faces : C → List C := fun _ => []
  /-- the names each has heard for each person: (person, name) -/
  names : C → List (C × N) := fun _ => []
  entries : List (Entry C N K A) := []
  done : List (C × A) := []

class HasNote (W : Type) (C N K A : outParam Type) where
  note : W → NoteState C N K A
  setNote : W → NoteState C N K A → W

inductive NoteEv (C N K A P : Type) where
  /-- `c` sees `x`'s face -/
  | see (c x : C) (s : Sight)
  /-- `x` tells `c` their name is `n` (true or not) -/
  | introduce (x c : C) (n : N)
  /-- `c` hears `n` given as `x`'s name by someone else -/
  | hearName (c x : C) (n : N)
  /-- `x` shows `c` an identity card: `c` sees the face and reads the real name -/
  | showId (x c : C)
  /-- `x` is shown on air under the name `n`, to everyone at the places `ps` -/
  | broadcast (x : C) (n : N) (ps : List P)
  /-- `c` gets a file with `x`'s photo and real name -/
  | dossier (c x : C)
  /-- `c` writes the name `n`, picturing `x` -/
  | write (c : C) (n : N) (x : C)
  /-- `c` adds the cause `k` to the latest entry for `x` -/
  | cause (c x : C) (k : K)
  /-- `c` adds details to the latest entry for `x`: actions before death, and the time of death
  (seconds after the details are written) -/
  | details (c x : C) (xs : List A) (dieIn : Option Nat)
  | pass (d : Nat)
  /-- the victim does what was written -/
  | act (x : C) (a : A)
  /-- narration check: the text says `x` died -/
  | died (x : C)
  /-- narration check: the text says `x` is alive -/
  | lives (x : C)
  /-- `c` gives `d` a page (or the note): `d` holds and has touched it -/
  | givePage (c d : C)
  /-- `c` touches the note or a page -/
  | touch (c : C)
  /-- narration check: `c` sees the shinigami -/
  | seeShinigami (c : C)
  | eyeDeal (c : C)
  deriving DecidableEq, Repr

/-- What the minds module can hold about the note. -/
inductive NoteFact (C N : Type) where
  | dead (x : C)
  /-- `n` is `x`'s real name -/
  | nameOf (x : C) (n : N)
  /-- `c` has seen `x`'s face -/
  | faceKnown (c x : C)
  /-- `c` knows `x`'s real name -/
  | nameKnown (c x : C)
  | touched (c : C)
  | owns (c : C)
  | eyes (c : C)
  deriving DecidableEq, Repr

/-- 40 seconds for a cause; 6 minutes 40 seconds for the details; 23 days for the actions. -/
def causeWindow : Nat := 40
def detailsWindow : Nat := 400
def actWindow : Nat := 23 * 86400

namespace NoteState
variable {C N K A : Type} [DecidableEq C] [DecidableEq N] [DecidableEq K] [DecidableEq A]
  (st : NoteState C N K A)

def set {β : Type} (f : C → β) (c : C) (b : β) : C → β := fun x => if x = c then b else f x

def heard (c x : C) (n : N) : Bool := (st.names c).contains (x, n)
def faceSeen (c x : C) : Bool := (st.faces c).contains x
def knowsName (c x : C) : Bool := st.heard c x (st.realName x)

/-- Someone else whose real name is `n` (a homonym of `x`), among `cast`. -/
def homonym (cast : List C) (n : N) (x : C) : Option C := cast.find? fun y => y != x && st.realName y == n

/-- The entry that will kill `x`: the first that took. -/
def fatal (x : C) : Option (Entry C N K A) :=
  st.entries.find? fun e => e.face == x && e.void.isNone

/-- The last entry written for `x` (taken or not). -/
def lastFor (x : C) : Option (Entry C N K A) :=
  (st.entries.filter (·.face == x)).getLast?

def addName (c x : C) (n : N) : NoteState C N K A :=
  if st.heard c x n then st else { st with names := set st.names c (st.names c ++ [(x, n)]) }

def addFace (c x : C) : NoteState C N K A :=
  let st := if st.faceSeen c x then st else { st with faces := set st.faces c (st.faces c ++ [x]) }
  if st.eyes c then st.addName c x (st.realName x) else st

/-- Replace the last entry for `x` by `f` of it. -/
def updateLast (x : C) (f : Entry C N K A → Entry C N K A) : NoteState C N K A :=
  let n := st.entries.length
  let i := ((List.range n).filter fun i => (st.entries[i]?.map (·.face == x)).getD false).getLast?
  match i with
  | some i => { st with entries := st.entries.modify i f }
  | none => st

end NoteState

/-- The second an entry's victim dies, given what has been written so far
(none: the entry never kills). -/
def Entry.due {C N K A : Type} (e : Entry C N K A) : Option Nat :=
  if e.void.isSome then none else
  match e.cause, e.causeVoid with
  | some _, none =>
    match e.detailsAt, e.detailsVoid with
    | some td, none => some (e.dieAt.getD td)
    | _, _ => some (e.causeAt + detailsWindow)
  | _, _ => some (e.t0 + causeWindow)

/-- How an entry kills (none: a heart attack). -/
def Entry.manner {C N K A : Type} (e : Entry C N K A) : Option K :=
  match e.cause, e.causeVoid with
  | some k, none => some k
  | _, _ => none

namespace NoteState
variable {C N K A : Type} [DecidableEq C] [DecidableEq N] [DecidableEq K] [DecidableEq A]
  (st : NoteState C N K A)

/-- Advance the clock to `t`; everyone whose death falls due by then dies. -/
def advance (cast : List C) (t : Nat) : NoteState C N K A :=
  let st := { st with now := t }
  cast.foldl (fun st x =>
    if !st.alive x then st else
    match st.fatal x with
    | some e => match e.due with
      | some d => if d ≤ t then { st with alive := set st.alive x false, deathAt := set st.deathAt x (some (d, e.manner)) } else st
      | none => st
    | none => st) st

end NoteState

/-- The words for a refusal. -/
def Refusal.text {C N K A : Type} [DecidableEq C] [DecidableEq N] (r : Refusal C N K A)
    (st : NoteState C N K A) : String :=
  let who := st.label
  let q (n : N) := s!"«{st.spell n}»"
  match r with
  | .dead c => s!"{who c} is dead"
  | .noPage c => s!"{who c} has no page of a Death Note"
  | .unheard c n x => s!"{who c} has never heard {q n} as {who x}'s name"
  | .noFace c x => s!"no face: {who c} has never seen {who x}'s face"
  | .fakeName n x h =>
    s!"a fake name: {q n} is not {who x}'s real name" ++ match h with
      | some y => s!" (it is {who y}'s, but {who y}'s face was not pictured, so a homonym is not affected)"
      | none => ""
  | .victimDead x => s!"{who x} is already dead"
  | .alreadyWritten x => s!"{who x}'s death is already written"
  | .noEntry => "there is no entry of theirs to add to"
  | .tooLateCause => "too late: no cause was written within 40 seconds, so it is a heart attack"
  | .causeImpossible k x => s!"the cause is impossible for them: {who x} cannot die of {(st.causes k).name}"
  | .causeHarms k y => s!"it would kill another: {(st.causes k).name} would kill {who y}"
  | .tooLateDetails => "too late: the details came more than 6 minutes 40 seconds after the cause"
  | .noCause => "details need a cause that stands"
  | .cannotDo a x => s!"the actions are impossible for them: {who x} could not {(st.actDefs a).name}"
  | .actHarms a y => s!"it would kill another: to {(st.actDefs a).name} would kill {who y}"
  | .tooLong => "the actions must be done within 23 days"
  | .notWritten x a => s!"nothing written makes {who x} {(st.actDefs a).name}"
  | .alreadyDone x a => s!"{who x} has already done it ({(st.actDefs a).name})"
  | .alive x => s!"{who x} is alive: no entry that took has killed them" ++
      match st.lastFor x with
      | some e => match e.void with
        | some (.noFace c y) => s!" (the last entry for them, {q e.name}, did not take: no face: {who c} had never seen {who y}'s face)"
        | some (.fakeName n y h) => s!" (the last entry for them, {q e.name}, did not take: a fake name: {q n} is not {who y}'s real name" ++
            (match h with | some z => s!"; it is {who z}'s, and a homonym whose face was not pictured is not affected)" | none => ")")
        | some _ => s!" (the last entry for them, {q e.name}, did not take)"
        | none => " yet"
      | none => " (no entry names them)"
  | .notOwner c => s!"only the owner can make the eye deal, and {who c} does not own the note"
  | .untouched c => s!"{who c} has never touched the note or a page, so cannot see its shinigami"
  | .hasEyes c => s!"{who c} already has the eyes"
  | .apart c x => s!"{who c} and {who x} are not together"
  | .refused r => "what was written for them was refused: " ++ match r with
    | .tooLateCause => "no cause within 40 seconds, so a heart attack at 40 seconds"
    | .causeImpossible k x => s!"the cause is impossible for them ({who x} cannot die of {(st.causes k).name}), so a heart attack at 40 seconds"
    | .causeHarms k y => s!"it would kill another ({(st.causes k).name} would kill {who y}), so a heart attack at 40 seconds"
    | .tooLateDetails => "the details came more than 6 minutes 40 seconds after the cause"
    | .cannotDo a x => s!"the actions are impossible for them ({who x} could not {(st.actDefs a).name})"
    | .actHarms a y => s!"it would kill another (to {(st.actDefs a).name} would kill {who y})"
    | .tooLong => "the actions must be done within 23 days"
    | _ => "the details need a cause that stands"

section
variable {W C N K A P : Type} [DecidableEq C] [DecidableEq N] [DecidableEq K] [DecidableEq A]
  [DecidableEq P] [HasNote W C N K A] [HasLoc W C P] [Cast C]
open HasNote NoteState

/-- Why the name `n`, written by `c` picturing `x`, does not take (none: it does).
Checked in this order: the face, the name, the victim. -/
def nameWhy (st : NoteState C N K A) (c : C) (n : N) (x : C) : Option (Refusal C N K A) :=
  if !st.faceSeen c x then some (.noFace c x)
  else if st.realName x != n then some (.fakeName n x (st.homonym Cast.all n x))
  else if !st.alive x then some (.victimDead x)
  else if (st.fatal x).isSome then some (.alreadyWritten x)
  else none

/-- Why the cause `k` does not stand (none: it does). -/
def causeWhy (st : NoteState C N K A) (e : Entry C N K A) (k : K) : Option (Refusal C N K A) :=
  let d := st.causes k
  if st.now > e.t0 + causeWindow then some .tooLateCause
  else if !d.possible e.face then some (.causeImpossible k e.face)
  else match d.harms.find? (· != e.face) with
    | some y => some (.causeHarms k y)
    | none => none

/-- Why the details are refused (none: they stand). -/
def detailsWhy (st : NoteState C N K A) (e : Entry C N K A) (xs : List A) (t : Option Nat) :
    Option (Refusal C N K A) :=
  if e.cause.isNone || e.causeVoid.isSome then some .noCause
  else if st.now > e.causeAt + detailsWindow then some .tooLateDetails
  else match xs.find? (fun a => !(st.actDefs a).able e.face) with
  | some a => some (.cannotDo a e.face)
  | none =>
    match xs.findSome? (fun a => ((st.actDefs a).harms.find? (· != e.face)).map (a, ·)) with
    | some (a, y) => some (.actHarms a y)
    | none => if t.getD 0 > actWindow then some .tooLong else none

/-- Why a move cannot be made (none: it can). -/
def noteWhy (w : W) : NoteEv C N K A P → Option (Refusal C N K A)
  | .see c x s =>
    let st := note w
    if !st.alive c then some (.dead c)
    else if s == .inPerson && (HasLoc.loc w c != HasLoc.loc w x || !st.alive x) then some (.apart c x)
    else none
  | .introduce x c _ | .showId x c =>
    let st := note w
    if !st.alive x then some (.dead x) else if !st.alive c then some (.dead c)
    else if HasLoc.loc w c != HasLoc.loc w x then some (.apart x c) else none
  | .hearName c _ _ | .dossier c _ | .touch c =>
    if (note w).alive c then none else some (.dead c)
  | .broadcast _ _ _ => none
  | .write c n x =>
    let st := note w
    if !st.alive c then some (.dead c)
    else if !st.holds c then some (.noPage c)
    else if !st.heard c x n then some (.unheard c n x)
    else none
  | .cause c x _ | .details c x _ _ =>
    let st := note w
    if !st.alive c then some (.dead c)
    else if !st.holds c then some (.noPage c)
    else match st.lastFor x with
      | none => some .noEntry
      | some e => if e.writer != c then some .noEntry else none
  | .pass _ => none
  | .act x a =>
    let st := note w
    match st.fatal x with
    | none => some (if st.alive x then .notWritten x a else .dead x)
    | some e =>
      match e.causeVoid, e.detailsVoid with
      | some r, _ => some (.refused r)
      | none, some r => some (.refused r)
      | none, none =>
      if !st.alive x then some (.dead x)
      else if e.detailsAt.isNone || !e.acts.contains a then some (.notWritten x a)
      else if st.done.contains (x, a) then some (.alreadyDone x a)
      else none
  | .died x => if (note w).alive x then some (.alive x) else none
  | .lives x => if (note w).alive x then none else some (.victimDead x)
  | .givePage c d =>
    let st := note w
    if !st.alive c then some (.dead c) else if !st.holds c then some (.noPage c)
    else if !st.alive d then some (.dead d)
    else if HasLoc.loc w c != HasLoc.loc w d then some (.apart c d) else none
  | .seeShinigami c =>
    let st := note w
    if !st.alive c then some (.dead c) else if !st.touched c then some (.untouched c) else none
  | .eyeDeal c =>
    let st := note w
    if st.owner != some c then some (.notOwner c)
    else if st.eyes c then some (.hasEyes c) else none

def noteStep (w : W) : NoteEv C N K A P → W
  | .see c x _ => setNote w ((note w).addFace c x)
  | .introduce x c n => setNote w ((note w).addName c x n)
  | .hearName c x n => setNote w ((note w).addName c x n)
  | .showId x c => let st := note w; setNote w ((st.addFace c x).addName c x (st.realName x))
  | .broadcast x n ps =>
    let st := note w
    setNote w ((Cast.all : List C).foldl (fun st c =>
      if st.alive c && ps.contains (HasLoc.loc w c) then (st.addFace c x).addName c x n else st) st)
  | .dossier c x => let st := note w; setNote w ((st.addFace c x).addName c x (st.realName x))
  | .write c n x =>
    let st := note w
    let e : Entry C N K A := { writer := c, name := n, face := x, t0 := st.now, void := nameWhy st c n x }
    setNote w { st with entries := st.entries ++ [e] }
  | .cause _ x k =>
    let st := note w
    setNote w (st.updateLast x fun e => { e with cause := some k, causeAt := st.now, causeVoid := causeWhy st e k })
  | .details _ x xs t =>
    let st := note w
    let f (e : Entry C N K A) : Entry C N K A :=
      { e with acts := xs, detailsAt := some st.now, dieAt := t.map (st.now + ·), detailsVoid := detailsWhy st e xs t }
    setNote w (st.updateLast x f)
  | .pass d => let st := note w; setNote w (st.advance Cast.all (st.now + d))
  | .act x a => let st := note w; setNote w { st with done := st.done ++ [(x, a)] }
  | .died _ | .lives _ | .seeShinigami _ => w
  | .givePage _ d =>
    let st := note w
    setNote w { st with holds := set st.holds d true, touched := set st.touched d true }
  | .touch c => let st := note w; setNote w { st with touched := set st.touched c true }
  | .eyeDeal c =>
    let st := note w
    setNote w { st with eyes := set st.eyes c true, life := set st.life c (st.life c / 2) }

instance : Domain W (NoteEv C N K A P) where
  ok w e := (noteWhy w e).isNone
  step := noteStep
  why w e := match noteWhy w e with
    | some r => r.text (note w)
    | none => ""

instance : Truth W (NoteFact C N) where
  truth w
    | .dead x => !(note w).alive x
    | .nameOf x n => (note w).realName x == n
    | .faceKnown c x => (note w).faceSeen c x
    | .nameKnown c x => (note w).knowsName c x
    | .touched c => (note w).touched c
    | .owns c => (note w).owner == some c
    | .eyes c => (note w).eyes c

end

/-- Only the living perceive. -/
instance (priority := low) {W C N K A : Type} [HasNote W C N K A] : Perceives W C where
  perceives w c := (HasNote.note w).alive c

/-- What a person knows and whether they are alive can change; real names cannot. -/
instance {C N : Type} : Fluent (NoteFact C N) where
  fluent
    | .nameOf .. => false
    | _ => true

/-! ## The checklist a write is judged by (for views and reports) -/

/-- One precondition, evaluated: an id, its kind (as in `studio/power-schema.md`),
a label, whether it holds, and what the module says when it does not. -/
structure Check where
  id : String
  kind : String
  label : String
  pass : Bool
  why : String
  deriving Repr

/-- Whether `c` writing `n` while picturing `x` takes: the face, the real
name, the victim alive, not already written. These are not preconditions of
the act (anyone with a page can write any name they have heard); they are what
decides whether it kills. -/
def takeChecks {C N K A : Type} [DecidableEq C] [DecidableEq N] (st : NoteState C N K A)
    (cast : List C) (c : C) (n : N) (x : C) : List Check :=
  let who := st.label
  let q := s!"«{st.spell n}»"
  [⟨"face", "knowledge", s!"{who c} has seen {who x}'s face", st.faceSeen c x,
     s!"no face: {who c} has never seen {who x}'s face"⟩,
   ⟨"realName", "knowledge", s!"{q} is {who x}'s real name", st.realName x == n,
     s!"a fake name: {q} is not {who x}'s real name" ++ match st.homonym cast n x with
      | some y => s!" (it is {who y}'s: a homonym, not pictured, is not affected)"
      | none => ""⟩,
   ⟨"victimAlive", "status", s!"{who x} is alive", st.alive x, s!"{who x} is already dead"⟩,
   ⟨"notWritten", "rule", s!"{who x}'s death is not already written", (st.fatal x).isNone,
     s!"{who x}'s death is already written"⟩]

end LangLib.World
