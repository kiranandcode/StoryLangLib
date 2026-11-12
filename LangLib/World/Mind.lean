import LangLib.World.Space

/-!
# Minds: beliefs, reasoning, observation, telling and lying

Each character holds beliefs, each with where it came from. A belief is a fact
(`atom φ`), its denial (`neg φ`), or a belief about someone else's belief
(`bel c b`), so "Kiran thinks Marcus knows the letter is in the office" is
`bel marcus (atom (letter in office))` in Kiran's list.

**Reasoning.** A story's `Lore` is a set of Horn rules over facts and denials
that every character reasons with ("whoever holds the letter has read it").
`view w c` is the closure of `c`'s own beliefs under the lore; `viewOf w c d`
is the closure of what `c` thinks `d` believes. `thinks` and `thinksThinks`
query them.

**Consistency.** A set of literals is consistent when it holds no fact
together with its denial, and no two facts that exclude each other
(`Supersedes`: one place per person, one place or hand per object).
`mindsConsistent` asks this of every character's view; a story can make it an
`Invariant`, so `Valid` rejects any story that leaves someone believing a
contradiction.

**Revision.** Beliefs remember their source. Seeing beats hearsay:
* what a character sees replaces anything it contradicts, and then any hearsay
  whose consequences contradict the new view is dropped;
* hearsay that contradicts something the listener saw, or would make their
  view inconsistent, is rejected: they only note that the speaker claimed it.

**Events.** Observation (`Perceive`): after any `Observable` event, everyone
present sees what it showed, and sees the others see it. `tell` is heard by
everyone present, `whisper` only by the listener; both need the speaker to
think what they say (inferred beliefs count), and `lie` needs them not to.
-/

namespace LangLib.World

inductive Belief (C Φ : Type) where
  | atom (φ : Φ)
  | neg (φ : Φ)
  | bel (c : C) (b : Belief C Φ)
  deriving DecidableEq, Repr

inductive Source (C : Type) where
  | seen
  | told (c : C)
  deriving DecidableEq, Repr

structure Held (C Φ : Type) where
  b : Belief C Φ
  src : Source C
  deriving DecidableEq, Repr

class HasMinds (W : Type) (C Φ : outParam Type) where
  beliefs : W → C → List (Held C Φ)
  setBeliefs : W → C → List (Held C Φ) → W

/-- A literal: a fact (`true`) or its denial (`false`). -/
abbrev BLit (Φ : Type) := Φ × Bool

/-- A rule everyone reasons with: if all of `body` then `head`. -/
structure LoreRule (Φ : Type) where
  body : List (BLit Φ)
  head : BLit Φ

class Lore (Φ : Type) where
  rules : List (LoreRule Φ)

instance (priority := low) {Φ : Type} : Lore Φ := ⟨[]⟩

/-- What is said: a fact, or (with `false`) its denial. -/
inductive MindEv (C Φ : Type) where
  /-- said aloud: everyone present hears -/
  | tell (c d : C) (l : Φ × Bool)
  /-- only `d` hears -/
  | whisper (c d : C) (l : Φ × Bool)
  /-- `c` says what they do not think -/
  | lie (c d : C) (l : Φ × Bool)
  deriving DecidableEq, Repr

variable {W C P Φ : Type} [DecidableEq C] [DecidableEq P] [DecidableEq Φ]
  [HasLoc W C P] [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ]

open HasLoc HasMinds

/-! ## Reasoning -/

def ofLit : BLit Φ → Belief C Φ
  | (φ, true) => .atom φ
  | (φ, false) => .neg φ

def litOf : Belief C Φ → Option (BLit Φ)
  | .atom φ => some (φ, true)
  | .neg φ => some (φ, false)
  | .bel _ _ => none

/-- Forward chaining with the lore, to a fixpoint (bounded by the number of rules). -/
def closure (ls : List (BLit Φ)) : List (BLit Φ) :=
  let step (ls : List (BLit Φ)) : List (BLit Φ) :=
    (Lore.rules (Φ := Φ)).foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) ls
  let rec go : Nat → List (BLit Φ) → List (BLit Φ)
    | 0, ls => ls
    | n + 1, ls => go n (step ls)
  go ((Lore.rules (Φ := Φ)).length + 1) ls

/-- Everything `c` believes, including what follows by the lore. -/
def view (w : W) (c : C) : List (BLit Φ) :=
  closure ((beliefs w c).filterMap (litOf ·.b))

/-- What `c` thinks `d` believes, closed under the lore. -/
def viewOf (w : W) (c d : C) : List (BLit Φ) :=
  closure ((beliefs w c).filterMap fun h => match h.b with
    | .bel d' b => if d' == d then litOf b else none
    | _ => none)

def thinks (w : W) (c : C) (φ : Φ) : Bool := (view w c).contains (φ, true)
def thinksNot (w : W) (c : C) (φ : Φ) : Bool := (view w c).contains (φ, false)
def thinksThinks (w : W) (c d : C) (φ : Φ) : Bool := (viewOf w c d).contains (φ, true)

/-- Held as stated (no inference). -/
def believes (w : W) (c : C) (b : Belief C Φ) : Bool := (beliefs w c).any (·.b == b)

/-- `c` thinks `φ` and it is true. -/
def knows (w : W) (c : C) (φ : Φ) : Bool := thinks w c φ && Truth.truth w φ

/-- `c` thinks `φ` but it is false. -/
def falseBelief (w : W) (c : C) (φ : Φ) : Bool := thinks w c φ && !Truth.truth w φ

/-! ## Consistency -/

def clash (x y : BLit Φ) : Bool :=
  (x.1 == y.1 && x.2 != y.2) ||
  (x.2 && y.2 && x.1 != y.1 && Supersedes.supersedes x.1 y.1)

def consistent (ls : List (BLit Φ)) : Bool :=
  ls.all fun x => ls.all fun y => !clash x y

def mindConsistent (w : W) (c : C) : Bool := consistent (view w c)

def mindsConsistent [Cast C] (w : W) : Bool := Cast.all.all (mindConsistent w)

/-! ## Learning and revision -/

private def contradicts (new old : Belief C Φ) : Bool :=
  match new, old with
  | .atom φ, .atom ψ => φ != ψ && Supersedes.supersedes φ ψ
  | .atom φ, .neg ψ => φ == ψ
  | .neg φ, .atom ψ => φ == ψ
  | .bel c b, .bel c' b' => c == c' && contradicts b b'
  | _, _ => false

private def add (hs : List (Held C Φ)) (h : Held C Φ) : List (Held C Φ) :=
  h :: hs.filter fun old => old.b != h.b && !contradicts h.b old.b

private def litsOf (hs : List (Held C Φ)) : List (BLit Φ) := closure (hs.filterMap (litOf ·.b))

/-- `c` sees `b`: it replaces what it contradicts, and hearsay that now clashes
with the closure is dropped. -/
def see (w : W) (c : C) (b : Belief C Φ) : W :=
  let hs := add (beliefs w c) ⟨b, .seen⟩
  let hs := if consistent (litsOf hs) then hs else
    hs.filter fun h => h.src == .seen || match litOf h.b with
      | some l => (litsOf (hs.filter (·.src == .seen))).all fun x => !clash l x
      | none => true
  setBeliefs w c hs

/-- `c` hears `b` from `d`: adopted unless it contradicts what `c` saw or would
make `c`'s view inconsistent; either way `c` notes that `d` claims it. -/
def hear (w : W) (c d : C) (b : Belief C Φ) : W :=
  let hs := beliefs w c
  let rejected := hs.any (fun h => h.src == .seen && contradicts b h.b) ||
    !consistent (litsOf (add hs ⟨b, .told d⟩))
  let hs := if rejected then hs else add hs ⟨b, .told d⟩
  setBeliefs w c (add hs ⟨.bel d b, .told d⟩)

/-- Everyone at `p` sees `φs`, and sees the others see them. -/
def witness [Cast C] (w : W) (p : P) (φs : List Φ) : W :=
  let present := Cast.all.filter fun x => loc w x == p
  present.foldl (fun w x =>
    (φs.flatMap fun φ => .atom φ :: (present.filter (· != x)).map fun y => .bel y (.atom φ)).foldl
      (fun w b => see w x b) w) w

instance [Cast C] : Domain W (MindEv C Φ) where
  ok w
    | .tell c d l | .whisper c d l => loc w c == loc w d && (view w c).contains l
    | .lie c d l => loc w c == loc w d && !(view w c).contains l
  step w
    | .tell c d l =>
      let hearers := (Cast.all.filter fun x => x != c && loc w x == loc w c)
      let w := hearers.foldl (fun w x => hear w x c (ofLit l)) w
      see w c (.bel d (ofLit l))
    | .whisper c d l | .lie c d l => see (hear w d c (ofLit l)) c (.bel d (ofLit l))
  why w
    | .tell c d _ | .whisper c d _ =>
      if loc w c != loc w d then "they are not together" else "the speaker does not think that"
    | .lie c d _ => if loc w c != loc w d then "they are not together"
                    else "the speaker thinks it is true, so it is not a lie"

/-- Witnessing: after each event, those present see what it showed. -/
instance {E : Type} [Cast C] [Observable W E Φ P] : Perceive W E where
  perceive before e after :=
    match Observable.seen before e with
    | some (p, φs) => witness after p φs
    | none => after

end LangLib.World
