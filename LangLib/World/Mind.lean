import LangLib.World.Space

/-!
# Minds: evidence, trust, ranked belief bases

Each character keeps an *evidence base*: everything they have come to believe,
each item with its source (`Evid`, after the evidential types of
Willett/Aikhenvald), a rank, a timestamp and how it entered. Nothing is ever
deleted; what a character believes now is computed from the base.

**Strength and attitude.** New information gets a strength: a prior for its
evidential type (seeing beats being told beats rumour) plus an adjustment from
`Credence`, which a story supplies (trust in the speaker, tension, persona
traits such as gullible or skeptical; see `Social.bondCredence`). The strength
picks the hearer's *attitude* (Baltag–Smets upgrades, Rodenhäuser's dynamic
attitudes):
* `hard`: self-knowledge; top rank;
* `radical`: accepted, and on a tie it outranks older items;
* `conservative`: accepted only where nothing of equal standing objects
  (stubborn characters take everything this way);
* `note`: not believed; the character only notes that the speaker said it
  (the reportative reading of hearsay).

**View.** `view w c` is the lore-closure of the *greedy consistent prefix* of
the base ordered by rank (then recency, by attitude): a linear base revision.
`view_consistent` proves the view is consistent whenever the lore is, so
consistency is a theorem, not a hope. Iterated revision comes free: an item
outranked today returns when what outranked it is itself outranked.

**Betrayal.** When something a character perceives clashes with what `d` told
them, `Credence.onBetrayal` fires once for that report (a story with
relationships lowers trust in `d`).

**Events.** Observation (`Perceive`): after any `Observable` event, everyone
present sees what it showed (and sees each other see it). `tell` is heard by
everyone present, `whisper` only by the listener, and both need the speaker to
think what they say; `lie` needs them not to. `notice c l e` is coming to
believe `l` by evidence `e`; a perception (`seen`, `sensed`) must be of
something true. `realise c l` is factive: `l` must be true and must follow
from what `c` already believes, which catches knowledge leaks in a text.
-/

namespace LangLib.World

inductive Belief (C Φ : Type) where
  | atom (φ : Φ)
  | neg (φ : Φ)
  | bel (c : C) (b : Belief C Φ)
  deriving DecidableEq, Repr

/-- Where a belief came from. -/
inductive Evid (C : Type) where
  | self | seen | sensed | inferred | assumed
  | told (c : C) | relayed (c : C) | rumour
  deriving DecidableEq, Repr

/-- How a belief entered the base. -/
inductive Upgrade | hard | radical | conservative | note
  deriving DecidableEq, Repr

structure Held (C Φ : Type) where
  b : Belief C Φ
  src : Evid C
  rank : Nat
  stamp : Nat
  up : Upgrade
  /-- the character has caught the source of this report out -/
  caught : Bool := false
  deriving DecidableEq, Repr

class HasMinds (W : Type) (C Φ : outParam Type) where
  beliefs : W → C → List (Held C Φ)
  setBeliefs : W → C → List (Held C Φ) → W

/-- How a character weighs information; supplied by the story. -/
class Credence (W C : Type) where
  /-- adjustment to the prior strength of evidence `e` for hearer `c` -/
  adj : W → C → Evid C → Int
  /-- strength at which `c` accepts information outright -/
  acceptAt : W → C → Int
  /-- `c` takes accepted information conservatively -/
  stubborn : W → C → Bool
  /-- `c` has caught `d` out -/
  onBetrayal : W → C → C → W

instance (priority := low) {W C : Type} : Credence W C :=
  ⟨fun _ _ _ => 0, fun _ _ => 3, fun _ _ => false, fun w _ _ => w⟩

/-- A literal: a fact (`true`) or its denial (`false`). -/
abbrev BLit (Φ : Type) := Φ × Bool

structure LoreRule (Φ : Type) where
  body : List (BLit Φ)
  head : BLit Φ

class Lore (Φ : Type) where
  rules : List (LoreRule Φ)

instance (priority := low) {Φ : Type} : Lore Φ := ⟨[]⟩

/-- What is said or noticed is a literal: a fact, or (with `false`) its denial. -/
inductive MindEv (C Φ : Type) where
  | tell (c d : C) (l : Φ × Bool)
  | whisper (c d : C) (l : Φ × Bool)
  | lie (c d : C) (l : Φ × Bool)
  | notice (c : C) (l : Φ × Bool) (e : Evid C)
  | realise (c : C) (l : Φ × Bool)
  deriving DecidableEq, Repr

namespace Evid
variable {C : Type}

def prior : Evid C → Int
  | .self => 6 | .seen => 5 | .sensed => 4 | .inferred => 3
  | .told _ => 3 | .relayed _ => 2 | .assumed => 1 | .rumour => 1

def speaker : Evid C → Option C
  | .told c | .relayed c => some c | _ => none

def perceptual : Evid C → Bool
  | .self | .seen | .sensed => true | _ => false

def testimony : Evid C → Bool
  | .told _ | .relayed _ | .rumour => true | _ => false
end Evid

variable {W C P Φ : Type} [DecidableEq C] [DecidableEq P] [DecidableEq Φ]
  [HasLoc W C P] [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ] [Credence W C]

open HasLoc HasMinds

/-! ## Reasoning -/

def ofLit : BLit Φ → Belief C Φ
  | (φ, true) => .atom φ
  | (φ, false) => .neg φ

def litOf : Belief C Φ → Option (BLit Φ)
  | .atom φ => some (φ, true)
  | .neg φ => some (φ, false)
  | .bel _ _ => none

/-- Forward chaining with the lore (bounded by the number of rules). -/
def closure (ls : List (BLit Φ)) : List (BLit Φ) :=
  let step (ls : List (BLit Φ)) : List (BLit Φ) :=
    (Lore.rules (Φ := Φ)).foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) ls
  let rec go : Nat → List (BLit Φ) → List (BLit Φ)
    | 0, ls => ls
    | n + 1, ls => go n (step ls)
  go ((Lore.rules (Φ := Φ)).length + 1) ls

def clash (x y : BLit Φ) : Bool :=
  (x.1 == y.1 && x.2 != y.2) ||
  (x.2 && y.2 && x.1 != y.1 && Supersedes.supersedes x.1 y.1)

def consistent (ls : List (BLit Φ)) : Bool :=
  ls.all fun x => ls.all fun y => !clash x y

/-- The greedy consistent prefix: keep each literal iff it is consistent, under
the lore, with what has been kept. -/
def admit (ls : List (BLit Φ)) : List (BLit Φ) :=
  ls.foldl (fun kept l => if consistent (closure (kept ++ [l])) then kept ++ [l] else kept) []

theorem admit_consistent_from (ls kept : List (BLit Φ))
    (h : consistent (closure kept) = true) :
    consistent (closure (ls.foldl (fun kept l =>
      if consistent (closure (kept ++ [l])) then kept ++ [l] else kept) kept)) = true := by
  induction ls generalizing kept with
  | nil => simpa using h
  | cons l ls ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _ (by assumption)
    · exact ih _ h

/-- Views are consistent whenever the lore is. -/
theorem admit_consistent (ls : List (BLit Φ))
    (h : consistent (closure ([] : List (BLit Φ))) = true) :
    consistent (closure (admit ls)) = true :=
  admit_consistent_from ls [] h

/-- Higher rank first; on a tie, a newer radical item goes first and a newer
conservative one goes last. -/
def before (x y : Held C Φ) : Bool :=
  x.rank > y.rank || (x.rank == y.rank &&
    (if x.stamp ≥ y.stamp then x.up != .conservative else y.up == .conservative))

def ordered (hs : List (Held C Φ)) : List (Held C Φ) := sortBy before hs

/-- What `c` believes now: the closure of the admitted part of their base. -/
def view (w : W) (c : C) : List (BLit Φ) :=
  closure (admit ((ordered (beliefs w c)).filterMap fun h =>
    if h.up == .note then none else litOf h.b))

/-- What `c` thinks `d` believes. -/
def viewOf (w : W) (c d : C) : List (BLit Φ) :=
  closure (admit ((ordered (beliefs w c)).filterMap fun h => match h.b with
    | .bel d' b => if d' == d then litOf b else none
    | _ => none))

theorem view_consistent (w : W) (c : C)
    (h : consistent (closure ([] : List (BLit Φ))) = true) :
    consistent (view w c) = true := admit_consistent _ h

def thinks (w : W) (c : C) (φ : Φ) : Bool := (view w c).contains (φ, true)
def thinksNot (w : W) (c : C) (φ : Φ) : Bool := (view w c).contains (φ, false)
def thinksThinks (w : W) (c d : C) (φ : Φ) : Bool := (viewOf w c d).contains (φ, true)

/-- In the base, believed or not. -/
def believes (w : W) (c : C) (b : Belief C Φ) : Bool := (beliefs w c).any (·.b == b)

def knows (w : W) (c : C) (φ : Φ) : Bool := thinks w c φ && Truth.truth w φ
def falseBelief (w : W) (c : C) (φ : Φ) : Bool := thinks w c φ && !Truth.truth w φ
def truthLit (w : W) (l : BLit Φ) : Bool := Truth.truth w l.1 == l.2

def mindConsistent (w : W) (c : C) : Bool := consistent (view w c)
def mindsConsistent [Cast C] (w : W) : Bool := Cast.all.all (mindConsistent w)

/-! ## Learning -/

def strength (w : W) (c : C) (e : Evid C) : Int := e.prior + Credence.adj w c e

/-- The hearer's attitude to information of strength `s`. -/
def attitude (w : W) (c : C) (e : Evid C) : Upgrade :=
  let s := strength w c e
  if e == .self then .hard
  else if s ≥ Credence.acceptAt w c then
    (if Credence.stubborn w c then .conservative else .radical)
  else if s ≥ Credence.acceptAt w c - 1 then .conservative
  else .note

private def stampOf (hs : List (Held C Φ)) : Nat := hs.foldl (fun m h => max m h.stamp) 0 + 1

private def insert (hs : List (Held C Φ)) (b : Belief C Φ) (e : Evid C) (u : Upgrade)
    (rank : Nat) : List (Held C Φ) :=
  hs ++ [{ b, src := e, rank, stamp := stampOf hs, up := u }]

/-- `c` comes to have `b` by evidence `e`. Testimony also records that the
speaker said it. A perception that clashes with an uncaught report from `d`
catches `d` out. -/
def learn (w : W) (c : C) (b : Belief C Φ) (e : Evid C) : W :=
  let u := attitude w c e
  let rank := if u == .hard then 10 else (strength w c e).toNat
  let hs := insert (beliefs w c) b e u rank
  let hs := match e.speaker with
    | some d => insert hs (.bel d b) e .radical rank
    | none => hs
  let w := setBeliefs w c hs
  if !e.perceptual then w else
  let v := view w c
  let liars := (beliefs w c).filterMap fun h =>
    match h.src.speaker, litOf h.b with
    | some d, some l => if !h.caught && h.up != .note && v.any (clash l) then some (h, d) else none
    | _, _ => none
  let w := setBeliefs w c ((beliefs w c).map fun h =>
    if liars.any (·.1 == h) then { h with caught := true } else h)
  liars.foldl (fun w (_, d) => Credence.onBetrayal w c d) w

/-- Everyone at `p` sees `φs`, and sees the others see them. -/
def witness [Cast C] (w : W) (p : P) (φs : List Φ) : W :=
  let present := Cast.all.filter fun x => loc w x == p
  present.foldl (fun w x =>
    (φs.flatMap fun φ => .atom φ :: (present.filter (· != x)).map fun y => .bel y (.atom φ)).foldl
      (fun w b => learn w x b .seen) w) w

instance [Cast C] : Domain W (MindEv C Φ) where
  ok w
    | .tell c d l | .whisper c d l => loc w c == loc w d && (view w c).contains l
    | .lie c d l => loc w c == loc w d && !(view w c).contains l
    | .notice _ l e => !e.perceptual || truthLit w l
    | .realise c l => truthLit w l && (closure (view w c)).contains l
  step w
    | .tell c d l =>
      let hearers := Cast.all.filter fun x => x != c && loc w x == loc w c
      let w := hearers.foldl (fun w x => learn w x (ofLit l) (.told c)) w
      learn w c (.bel d (ofLit l)) .self
    | .whisper c d l | .lie c d l => learn (learn w d (ofLit l) (.told c)) c (.bel d (ofLit l)) .self
    | .notice c l e => learn w c (ofLit l) e
    | .realise c l => learn w c (ofLit l) .inferred
  why w
    | .tell c d _ | .whisper c d _ =>
      if loc w c != loc w d then "they are not together" else "the speaker does not think that"
    | .lie c d _ => if loc w c != loc w d then "they are not together"
                    else "the speaker thinks it is true, so it is not a lie"
    | .notice _ _ _ => "a perception must be of something true"
    | .realise _ l => if !truthLit w l then "the text says they know it, but it is false"
                      else "they have no way to know that"

/-- Witnessing: after each event, those present see what it showed. -/
instance {E : Type} [Cast C] [Observable W E Φ P] : Perceive W E where
  perceive before e after :=
    match Observable.seen before e with
    | some (p, φs) => witness after p φs
    | none => after

end LangLib.World
