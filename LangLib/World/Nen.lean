import LangLib.World.Mind

/-!
# Nen (the power system of *Hunter x Hunter*)

A second story-specific power system, in the style of `Magic.lean` but with
the machinery a Nen fight turns on: abilities whose activation has
conditions, and what each fighter can see of the other's.

* **Types and affinity.** Six types round a hexagon (enhancer, transmuter,
  conjurer, specialist, manipulator, emitter); a user masters their own type
  fully and 20% less per step away (`NenType.affinity`).
* **Techniques** (`Tech`): Ten, Zetsu, Ren, Gyo, In, En, Ken, Ko, Ryu. Taking
  one up costs aura; Zetsu shuts the flow of aura off (no other technique, no
  Hatsu); Ko puts all of it in one point (no Ken or Ryu). Gyo is what lets a
  fighter `spot` aura hidden by In; Ko and Ken change what a blow does.
* **Aura** is a resource: techniques and abilities cost it.
* **Abilities** (Hatsu) are data (`AbilityDef`): type, cost, which hands they
  need, their effect, whether they are maintained, and their *vows*
  (restrictions their owner took on, which strengthen them: `power`).
* **Skill Hunter.** A stolen ability lives on a page of the thief's book. It
  can be activated only while the book is held (in the right hand) open at its
  page, or while its page holds the one bookmark; a maintained one ends as soon
  as neither holds (`prune`), and its marks go with it, unless it is
  *post-mortem* Nen (its owner is dead and his Nen got stronger for it): then
  its marks stay, and so do the copies they are on. A stolen ability whose
  owner has died is gone from the book, unless it is post-mortem.
* **Bodies.** People and copies (puppets, made by an ability with the `copy`
  effect). A body can be marked (seals, antennae, stamps, gum), can wear
  someone else's likeness, can lose its head (a stamped puppet stops) or a
  hand.

Validity is whether each move's preconditions hold: the ability's conditions,
enough aura, a hand free while the book is held, the target in reach, a puppet
under control. `why` says which failed, in words.

**What fighters see.** An ability used in the open shows everyone present
that its user has it, and the marks it leaves (`Observable`, read by the minds
module). Used by someone hidden in a crowd, or under In, it shows nothing; a
fighter with Gyo up can `spot` In-hidden aura on a body and comes to know it.
-/

namespace LangLib.World

inductive NenType | enhancer | transmuter | conjurer | specialist | manipulator | emitter
  deriving DecidableEq, Repr

namespace NenType
/-- Clockwise round the hexagon. -/
def pos : NenType → Nat
  | .enhancer => 0 | .transmuter => 1 | .conjurer => 2 | .specialist => 3
  | .manipulator => 4 | .emitter => 5

def dist (a b : NenType) : Nat :=
  let d := if a.pos ≥ b.pos then a.pos - b.pos else b.pos - a.pos
  min d (6 - d)

/-- How much of an ability of type `t` a user of type `u` can master, in
percent: all of their own type, 20 less for each step round the hexagon; only
specialists have specialist abilities at all. -/
def affinity (u t : NenType) : Nat :=
  if t == .specialist && u != .specialist then 0 else 100 - 20 * dist u t
end NenType

inductive Tech | ten | zetsu | ren | gyo | in_ | en | ken | ko | ryu
  deriving DecidableEq, Repr

namespace Tech
def cost : Tech → Nat
  | .ten | .zetsu => 0 | .gyo | .in_ | .ryu => 1 | .ren | .ken => 2 | .en | .ko => 3

/-- Techniques that cannot be held at once. -/
def excludes : Tech → Tech → Bool
  | .zetsu, t | t, .zetsu => t != .zetsu
  | .ko, .ken | .ken, .ko | .ko, .ryu | .ryu, .ko => true
  | _, _ => false
end Tech

inductive Hand | left | right | both
  deriving DecidableEq, Repr

/-- The hands an ability needs free to be activated. -/
inductive HandRule
  /-- none: aura from anywhere (Bungee Gum from a foot) -/
  | none
  /-- the hand it is activated with (both, where the ability has a two-handed use) -/
  | one
  /-- both hands, whichever is used -/
  | both
  deriving DecidableEq, Repr

/-- What an ability does to its target. -/
inductive Effect
  /-- Sun and Moon: a sun with the left hand, a moon with the right -/
  | seal
  /-- Black Voice: an antenna; the body obeys its user -/
  | antenna
  /-- Order Stamp: a stamped puppet obeys simple orders -/
  | stamp
  /-- Gallery Fake: the target (a copy not yet made) appears, a puppet copy of its original -/
  | copy
  /-- Convert Hands: right hand, the target takes the user's likeness; left, the
  user takes the target's; both, they swap -/
  | likeness
  /-- Bungee Gum: aura with the properties of rubber and gum, stuck to the target -/
  | gum
  /-- Texture Surprise: a thin sheet of aura that shows a false surface -/
  | texture
  | none
  deriving DecidableEq, Repr

/-- Which bodies an ability can be used on. -/
inductive Target | any | puppet | person
  deriving DecidableEq, Repr

structure AbilityDef where
  name : String
  type : NenType
  cost : Nat
  hands : HandRule := .one
  effect : Effect := .none
  /-- stays active until released or (for a stolen one) until its page loses support -/
  sustained : Bool := false
  /-- lives on a page of a Skill Hunter book -/
  stolen : Bool := false
  ownerAlive : Bool := true
  /-- Nen made stronger by its owner's death: it, and what it marks, outlive him -/
  postMortem : Bool := false
  /-- restrictions its owner took on; each makes it stronger -/
  vows : List String := []
  /-- how many bodies one user can hold with it at once (0: no limit) -/
  limit : Nat := 0
  target : Target := .any
  deriving DecidableEq, Repr

inductive MarkKind | sun | moon | antenna | stamp | gum | texture
  deriving DecidableEq, Repr

structure Mark (C Ab : Type) where
  kind : MarkKind
  by_ : C
  ab : Ab
  /-- a seal held on for three to five seconds: a complete bomb -/
  full : Bool := false
  /-- made under In: only Gyo sees it -/
  hidden : Bool := false
  deriving DecidableEq, Repr

/-- A Skill Hunter book: held in the right hand, open at a page, one bookmark. -/
structure Book (Ab : Type) where
  held : Bool := false
  page : Option Ab := none
  mark : Option Ab := none
  deriving DecidableEq, Repr

inductive Body | person | copy
  deriving DecidableEq, Repr

structure NenState (C Ab : Type) where
  defs : Ab → AbilityDef
  type : C → NenType
  /-- a character's own abilities and the pages of their book -/
  owns : C → List Ab
  body : C → Body
  /-- the original a copy is made from (a person is their own) -/
  orig : C → C
  aura : C → Nat
  techs : C → List Tech
  /-- alive (a person) or made and not destroyed (a copy) -/
  present : C → Bool
  headed : C → Bool := fun _ => true
  hands : C → List Hand := fun _ => [.left, .right]
  hurt : C → Nat := fun _ => 0
  book : C → Book Ab := fun _ => {}
  active : List (C × Ab) := []
  marks : C → List (Mark C Ab) := fun _ => []
  /-- whose likeness a body wears -/
  looks : C → C
  /-- blended into a crowd: what they do there is not seen -/
  hidden : C → Bool := fun _ => false

class HasNen (W : Type) (C Ab : outParam Type) where
  nen : W → NenState C Ab
  setNen : W → NenState C Ab → W

inductive NenEv (C Ab : Type) where
  | tech (c : C) (t : Tech)
  | untech (c : C) (t : Tech)
  | openBook (c : C) (a : Ab)
  | closeBook (c : C)
  /-- put the one bookmark in the page the book is open at -/
  | bookmark (c : C) (a : Ab)
  | use (c : C) (a : Ab) (t : C) (h : Hand)
  /-- hold a seal on `t` for three to five seconds: a complete bomb -/
  | charge (c t : C)
  | release (c : C) (a : Ab)
  /-- `c` commands a body they control -/
  | order (c x : C)
  | behead (c x : C)
  /-- a sun on `x` touches a moon on `y` -/
  | detonate (x y : C)
  /-- with Gyo, `c` sees the hidden aura on `x` -/
  | spot (c x : C)
  | strike (c t : C) (n : Nat)
  | lose (c : C) (h : Hand)
  | hide (c : C)
  | emerge (c : C)
  deriving DecidableEq, Repr

inductive NenFact (C Ab : Type) where
  | can (c : C) (a : Ab)
  | active (c : C) (a : Ab)
  | marked (x : C) (k : MarkKind)
  | looksLike (x y : C)
  /-- the body `x` is the person `y` -/
  | is (x y : C)
  /-- the ability needs both hands free at once -/
  | needsBothHands (a : Ab)
  /-- the ability is worked with both hands (one each, or both together) -/
  | usesBothHands (a : Ab)
  | gone (x : C)
  deriving DecidableEq, Repr

namespace NenState
variable {C Ab : Type} [DecidableEq C] [DecidableEq Ab] (st : NenState C Ab)

def set {β : Type} (f : C → β) (c : C) (b : β) : C → β := fun x => if x = c then b else f x

def has (c : C) (t : Tech) : Bool := (st.techs c).contains t

def free (c : C) : Hand → Bool
  | .left => (st.hands c).contains .left
  | .right => (st.hands c).contains .right && !(st.book c).held
  | .both => (st.hands c).contains .left && (st.hands c).contains .right && !(st.book c).held

/-- A stolen ability can be used while its page is open in the held book or
bookmarked; a character's own ability always. -/
def supported (c : C) (a : Ab) : Bool :=
  !(st.defs a).stolen || ((st.book c).held && (st.book c).page == some a) || (st.book c).mark == some a

/-- `c` has `a` (their own, or a page of their book whose owner's Nen still holds). -/
def can (c : C) (a : Ab) : Bool :=
  (st.owns c).contains a && ((st.defs a).ownerAlive || (st.defs a).postMortem)

def sealed (x : C) : Bool := (st.marks x).any fun m => (st.defs m.ab).postMortem

def controlledBy (c x : C) : Bool :=
  st.present x && (st.marks x).any fun m =>
    m.by_ == c && (m.kind == .antenna || (m.kind == .stamp && st.headed x))

def controlled (x : C) : Bool := (st.marks x).any fun m =>
  m.kind == .antenna || (m.kind == .stamp && st.headed x)

/-- Moves of its own accord: a living person, or a body under someone's control. -/
def mobile (x : C) : Bool := st.present x && (st.body x == .person || st.controlled x)

def addMark (x : C) (m : Mark C Ab) : NenState C Ab := { st with marks := set st.marks x (st.marks x ++ [m]) }

/-- Ability `a` of `c` ends: its marks go unless it is post-mortem Nen; copies
vanish unless something post-mortem marks them; likenesses come undone. -/
def endAbility (c : C) (a : Ab) (cast : List C) : NenState C Ab :=
  let d := st.defs a
  let st := if d.postMortem then st else
    { st with marks := fun x => (st.marks x).filter fun m => !(m.by_ == c && m.ab == a) }
  match d.effect with
  | .copy => if d.postMortem then st else
      { st with present := fun x => st.present x && (st.body x != .copy || st.sealed x || !cast.contains x) }
  | .likeness => { st with looks := st.orig }
  | _ => st

/-- After the book changes: maintained stolen abilities whose page lost its
support end. -/
def prune (cast : List C) : NenState C Ab :=
  let gone := st.active.filter fun (c, a) => !st.supported c a
  let st' := { st with active := st.active.filter fun (c, a) => st.supported c a }
  gone.foldl (fun s (c, a) => s.endAbility c a cast) st'

end NenState

section
variable {W C Ab : Type} [DecidableEq C] [DecidableEq Ab] [HasNen W C Ab]
open HasNen NenState

/-- Why `c` cannot activate `a` on `t` with `h` (none: they can). -/
def useWhy {P : Type} [DecidableEq P] [HasLoc W C P] (w : W) (c : C) (a : Ab) (t : C) (h : Hand) :
    Option String :=
  let st := nen w
  let d := st.defs a
  let loc := HasLoc.loc w
  -- a copy is made where its original is
  let reach := if d.effect == .copy then st.orig t else t
  if !st.present c then some "they are dead"
  else if st.has c .zetsu then some "in Zetsu no aura flows, so no Hatsu"
  else if !(st.owns c).contains a then some s!"they do not have {d.name}"
  else if !d.ownerAlive && !d.postMortem then some s!"the owner of {d.name} is dead, so it has gone from the book"
  else if !st.supported c a then some s!"the book is neither open at {d.name} nor bookmarked there"
  else if d.effect == .seal && h == .both then some "a seal is made with one hand: the sun with the left, the moon with the right"
  else if !(match d.hands with
      | .none => true
      | .one => st.free c h
      | .both => st.free c .both) then
    some (if d.hands == .both then s!"{d.name} needs both hands free" ++ (if (st.book c).held then " (the right one holds the book)" else "")
          else if h == .right && (st.book c).held then s!"the right hand holds the book" else "that hand is not free")
  else if st.aura c < d.cost then some s!"not enough aura ({st.aura c} < {d.cost})"
  else if loc reach != loc c || !st.present reach then some "the target is out of reach"
  else if d.effect == .copy && (st.body t != .copy || st.present t) then some "only a copy not yet made can be made"
  else if d.target == .puppet && (st.body t != .copy || !st.headed t) then some s!"{d.name} only works on a puppet with its head"
  else if d.target == .person && st.body t != .person then some s!"{d.name} only works on people"
  else none

/-- Bodies one user holds with an ability (counted over a finite cast). -/
def holdsCount (st : NenState C Ab) (cast : List C) (c : C) (a : Ab) : Nat :=
  (cast.filter fun x => st.present x && (st.marks x).any fun m => m.by_ == c && m.ab == a).length

def useStep (st : NenState C Ab) (c : C) (a : Ab) (t : C) (h : Hand) : NenState C Ab :=
  let d := st.defs a
  let st := { st with aura := set st.aura c (st.aura c - d.cost),
                      active := if d.sustained && !st.active.contains (c, a) then st.active ++ [(c, a)] else st.active }
  let mk (k : MarkKind) : Mark C Ab := { kind := k, by_ := c, ab := a, hidden := st.has c .in_ }
  match d.effect with
  | .seal => st.addMark t (mk (if h == .left then .sun else .moon))
  | .antenna => st.addMark t (mk .antenna)
  | .stamp => st.addMark t (mk .stamp)
  | .gum => st.addMark t (mk .gum)
  | .texture => st.addMark t (mk .texture)
  | .copy => { st with present := set st.present t true, looks := set st.looks t (st.looks (st.orig t)) }
  | .likeness => match h with
    | .right => { st with looks := set st.looks t (st.looks c) }
    | .left => { st with looks := set st.looks c (st.looks t) }
    | .both => { st with looks := set (set st.looks t (st.looks c)) c (st.looks t) }
  | .none => st

instance : Truth W (NenFact C Ab) where
  truth w
    | .can c a => (nen w).can c a
    | .active c a => (nen w).active.contains (c, a)
    | .marked x k => ((nen w).marks x).any (·.kind == k)
    | .looksLike x y => (nen w).looks x == y
    | .is x y => x == y
    | .needsBothHands a => ((nen w).defs a).hands == .both
    | .usesBothHands a => ((nen w).defs a).hands == .both ||
        (((nen w).defs a).hands == .one && (((nen w).defs a).effect == .seal || ((nen w).defs a).effect == .likeness))
    | .gone x => !(nen w).present x

variable {P Φ : Type} [DecidableEq P] [DecidableEq Φ] [HasLoc W C P] [Cast C]
  [HasMinds W C Φ] [Inject (NenFact C Ab) Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ]
  [Credence W C Φ] [Fluent Φ] [Clock W] [PartialLoc W C]

def nenWhy (w : W) : NenEv C Ab → Option String
  | .tech c t =>
    let st := nen w
    if !st.present c then some "they are dead"
    else if st.has c t then some "they already have it up"
    else if (st.techs c).any (Tech.excludes t) then some "it cannot be held with what they already have up"
    else if st.aura c < t.cost then some s!"not enough aura ({st.aura c} < {t.cost})"
    else none
  | .untech c t => if (nen w).has c t then none else some "they do not have it up"
  | .openBook c a =>
    let st := nen w
    if !st.present c then some "they are dead"
    else if !(st.owns c).contains a || !(st.defs a).stolen then some "that is not a page of their book"
    else if !(st.hands c).contains .right then some "the book is held in the right hand"
    else if st.has c .zetsu then some "in Zetsu no aura flows, so no book"
    else none
  | .closeBook c => if ((nen w).book c).held then none else some "they are not holding the book"
  | .bookmark c a =>
    let st := nen w
    if (st.book c).held && (st.book c).page == some a then none
    else some "the bookmark goes in the page the book is open at"
  | .use c a t h =>
    let st := nen w
    match useWhy w c a t h with
    | some why => some why
    | none =>
      let d := st.defs a
      if d.limit != 0 && d.limit ≤ holdsCount st Cast.all c a then
        some s!"{d.name} holds at most {d.limit} at once"
      else none
  | .charge c t =>
    let st := nen w
    if !st.present c then some "they are dead"
    else if HasLoc.loc w c != HasLoc.loc w t then some "the target is out of reach"
    else if !(st.marks t).any (fun m => m.by_ == c && (m.kind == .sun || m.kind == .moon) && !m.full) then
      some "there is no seal of theirs on it to hold"
    else if st.aura c < 1 then some "not enough aura"
    else none
  | .release c a => if (nen w).active.contains (c, a) then none else some "it is not active"
  | .order c x => if (nen w).controlledBy c x then none else some "they do not control that body"
  | .behead c x =>
    let st := nen w
    if !st.present c then some "they are dead"
    else if c == x then some "not themselves"
    else if HasLoc.loc w c != HasLoc.loc w x || !st.present x then some "the target is out of reach"
    else if !st.headed x then some "it has no head"
    else none
  | .detonate x y =>
    let st := nen w
    let sun := (st.marks x).filter (·.kind == .sun)
    let moon := (st.marks y).filter (·.kind == .moon)
    if !st.present x || !st.present y then some "a sealed body is gone"
    else if HasLoc.loc w x != HasLoc.loc w y then some "the seals are not together"
    else if !sun.any fun s => moon.any fun m => s.by_ == m.by_ && s.ab == m.ab then
      some "no sun on the one and moon on the other"
    else if !st.mobile x && !st.mobile y then
      some "neither body can move to bring the seals together (a puppet without its head, nobody controlling it)"
    else none
  | .spot c x =>
    let st := nen w
    if !st.has c .gyo then some "without Gyo, aura hidden by In cannot be seen"
    else if HasLoc.loc w c != HasLoc.loc w x then some "it is out of sight"
    else if !(st.marks x).any (·.hidden) then some "there is no hidden aura on it"
    else none
  | .strike c t _ =>
    let st := nen w
    if !st.present c then some "they are dead"
    else if c == t then some "not themselves"
    else if HasLoc.loc w c != HasLoc.loc w t || !st.present t then some "the target is out of reach"
    else none
  | .lose c h => if ((nen w).hands c).contains h then none else some "they have already lost it"
  | .hide c => if (nen w).hidden c then some "they are already hidden" else none
  | .emerge c => if (nen w).hidden c then none else some "they are not hidden"

def nenStep (w : W) : NenEv C Ab → W
  | .tech c t =>
    let st := nen w
    setNen w { st with techs := set st.techs c (st.techs c ++ [t]), aura := set st.aura c (st.aura c - t.cost) }
  | .untech c t => let st := nen w; setNen w { st with techs := set st.techs c ((st.techs c).erase t) }
  | .openBook c a =>
    let st := nen w
    setNen w ({ st with book := set st.book c { st.book c with held := true, page := some a } }.prune Cast.all)
  | .closeBook c =>
    let st := nen w
    setNen w ({ st with book := set st.book c { st.book c with held := false, page := none } }.prune Cast.all)
  | .bookmark c a =>
    let st := nen w
    setNen w ({ st with book := set st.book c { st.book c with mark := some a } }.prune Cast.all)
  | .use c a t h => setNen w (useStep (nen w) c a t h)
  | .charge c t =>
    let st := nen w
    setNen w { st with
      aura := set st.aura c (st.aura c - 1),
      marks := set st.marks t ((st.marks t).map fun m =>
        if m.by_ == c && (m.kind == .sun || m.kind == .moon) then { m with full := true } else m) }
  | .release c a =>
    let st := nen w
    setNen w ({ st with active := st.active.erase (c, a) }.endAbility c a Cast.all)
  | .order _ _ => w
  | .behead _ x =>
    let st := nen w
    setNen w { st with
      headed := set st.headed x false
      present := if st.body x == .person then set st.present x false else st.present
      marks := set st.marks x ((st.marks x).filter (·.kind != .stamp)) }
  | .detonate x y =>
    let st := nen w
    let full := ((st.marks x) ++ (st.marks y)).any fun m => (m.kind == .sun || m.kind == .moon) && m.full
    let hit := Cast.all.filter fun z => z != x && z != y && st.present z && HasLoc.loc w z == HasLoc.loc w x
    let st := { st with present := set (set st.present x false) y false,
                        marks := set (set st.marks x []) y [] }
    setNen w (hit.foldl (fun s z => { s with hurt := set s.hurt z (s.hurt z + if full then 4 else 1) }) st)
  | .spot c x =>
    ((nen w).marks x).foldl (fun w m =>
      if m.hidden then learn w c (.atom (ev (NenFact.marked x m.kind : NenFact C Ab))) .seen else w) w
  | .strike c t n =>
    let st := nen w
    let n := if st.has c .ko then 2 * n else n
    let n := if st.has t .ken then n - 1 else n
    setNen w { st with hurt := set st.hurt t (st.hurt t + n) }
  | .lose c h => let st := nen w; setNen w { st with hands := set st.hands c ((st.hands c).erase h) }
  | .hide c => let st := nen w; setNen w { st with hidden := set st.hidden c true }
  | .emerge c => let st := nen w; setNen w { st with hidden := set st.hidden c false }

instance : Domain W (NenEv C Ab) where
  ok w e := (nenWhy w e).isNone
  step := nenStep
  why w e := (nenWhy w e).getD ""

/-- What an ability used in the open shows those present: that its user has it,
and the marks or likeness it leaves. From someone hidden, or under In, nothing. -/
instance : Observable W (NenEv C Ab) Φ P where
  seen w
    | .use c a t h =>
      let st := nen w
      if st.hidden c || st.has c .in_ || st.looks c != c then none else
      let d := st.defs a
      let shows : List (NenFact C Ab) := match d.effect with
        | .seal => [.marked t (if h == .left then .sun else .moon)]
        | .antenna => [.marked t .antenna]
        | .stamp => [.marked t .stamp]
        | .gum => [.marked t .gum]
        | .likeness => match h with
          | .right => [.looksLike t (st.looks c)]
          | .left => [.looksLike c (st.looks t)]
          | .both => [.looksLike t (st.looks c), .looksLike c (st.looks t)]
        | _ => []
      some (HasLoc.loc w c, (NenFact.can c a :: (if d.sustained then [NenFact.active c a] else []) ++ shows).map ev)
    | .detonate x y => some (HasLoc.loc w x, [ev (NenFact.gone x : NenFact C Ab), ev (NenFact.gone y : NenFact C Ab)])
    | _ => none

end

instance {C Ab : Type} [DecidableEq C] [DecidableEq Ab] : Supersedes (NenFact C Ab) where
  supersedes
    | .looksLike x _, .looksLike x' _ => x == x'
    | _, _ => false

/-- What is active, marked or worn can change; who has what, who is who, and
what was destroyed cannot. -/
instance {C Ab : Type} : Fluent (NenFact C Ab) where
  fluent
    | .active .. | .marked .. | .looksLike .. => true
    | _ => false

/-- An ability's strength in `c`'s hands, in percent: their affinity with its
type (a stolen one keeps its owner's mastery), raised by a quarter for each vow. -/
def NenState.power {C Ab : Type} (st : NenState C Ab) (c : C) (a : Ab) : Nat :=
  let d := st.defs a
  (if d.stolen then 100 else NenType.affinity (st.type c) d.type) * (4 + d.vows.length) / 4

end LangLib.World
