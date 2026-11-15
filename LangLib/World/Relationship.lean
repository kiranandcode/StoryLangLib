import LangLib.World.Domain

/-!
# Relationships as kinds that change: friends to lovers

`Social`'s bonds are levels (trust, attraction, affection, tension). A story
like friends-to-lovers is about something else: what *kind* of relationship
two people have, and how it changes. Some kinds hold by mutual declaration
(partners, exclusive), some by deed (lovers: they have slept together), and
some are old facts of history (childhood best friends). A declaration by one
side is a proposal, not a change: "you're mine" said by one person makes
nobody partners until the other accepts.

* `propose a b k`: `a` declares or asks for relationship `k` with `b`;
* `accept b a k`: `b` takes up `a`'s proposal; the kind now holds both ways;
* `decline b a k`, `end a b k`: a proposal refused, a kind given up (either
  side can end one; it takes both to start one);
* `consummate a b`: a deed that makes them lovers (the story decides which
  deed; with `Consent`, a consented sex act).

`kinds w a b` is what holds between them now; `pending w a b` the proposals
still open. Kinds are symmetric: the state stores unordered pairs.
-/

namespace LangLib.World

inductive RelKind | acquaintances | friends | bestFriends | lovers | partners | exclusive
  deriving DecidableEq, Repr

def RelKind.name : RelKind → String
  | .acquaintances => "acquaintances" | .friends => "friends" | .bestFriends => "bestFriends"
  | .lovers => "lovers" | .partners => "partners" | .exclusive => "exclusive"

/-- Kinds that need both people's word (lovers can also come by deed). -/
def RelKind.declared : RelKind → Bool
  | .partners | .exclusive => true
  | _ => false

structure RelState (C : Type) where
  /-- (a, b, k): `k` holds between `a` and `b` (either order) -/
  holds : List (C × C × RelKind) := []
  /-- (proposer, to, k) -/
  proposals : List (C × C × RelKind) := []
  deriving DecidableEq, Repr

class HasRel (W : Type) (C : outParam Type) where
  rel : W → RelState C
  setRel : W → RelState C → W

inductive RelEv (C : Type) where
  | propose (a b : C) (k : RelKind)
  | accept (b a : C) (k : RelKind)
  | decline (b a : C) (k : RelKind)
  | «end» (a b : C) (k : RelKind)
  | consummate (a b : C)
  deriving DecidableEq, Repr

variable {W C : Type} [DecidableEq C] [HasRel W C]
open HasRel

def RelState.has (s : RelState C) (a b : C) (k : RelKind) : Bool :=
  s.holds.any fun (x, y, j) => j == k && ((x == a && y == b) || (x == b && y == a))

def RelState.kinds (s : RelState C) (a b : C) : List RelKind :=
  [.acquaintances, .friends, .bestFriends, .lovers, .partners, .exclusive].filter (s.has a b)

def RelState.pending (s : RelState C) (a b : C) : List RelKind :=
  (s.proposals.filter fun (x, y, _) => (x == a && y == b) || (x == b && y == a)).map (·.2.2)

def RelState.add (s : RelState C) (a b : C) (k : RelKind) : RelState C :=
  if s.has a b k then s else { s with holds := (a, b, k) :: s.holds }

def relOk3 (s : RelState C) : RelEv C → Tri
  | .accept b a k | .decline b a k => Tri.ofBool (s.proposals.contains (a, b, k))
  | .end a b k => Tri.ofBool (s.has a b k)
  | .propose a b _ => Tri.ofBool (a != b)
  | .consummate a b => Tri.ofBool (a != b)

def relStep (s : RelState C) : RelEv C → RelState C
  | .propose a b k =>
    if s.has a b k || s.proposals.contains (a, b, k) then s
    else { s with proposals := (a, b, k) :: s.proposals }
  | .accept b a k => { (s.add a b k) with proposals := s.proposals.erase (a, b, k) }
  | .decline b a k => { s with proposals := s.proposals.erase (a, b, k) }
  | .end a b k => { s with holds := s.holds.filter fun (x, y, j) =>
      !(j == k && ((x == a && y == b) || (x == b && y == a))) }
  | .consummate a b => s.add a b .lovers

instance : Domain W (RelEv C) where
  ok3 w e := relOk3 (rel w) e
  ok w e := relOk3 (rel w) e == .yes
  step w e := setRel w (relStep (rel w) e)
  why _
    | .accept _ _ _ | .decline _ _ _ => "nobody proposed that"
    | .end _ _ _ => "they aren't that to each other"
    | _ => "a relationship needs two people"

/-- One person's word changes nothing that needs both: a proposal leaves the
kinds as they were. -/
theorem propose_kinds (s : RelState C) (a b : C) (k : RelKind) (x y : C) :
    (relStep s (.propose a b k)).kinds x y = s.kinds x y := by
  simp only [relStep]; split <;> rfl

end LangLib.World
