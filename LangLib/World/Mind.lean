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
present who can perceive (`Perceives`; by default everyone) sees what it
showed (and sees each other see it). `tell` is heard by
everyone present who can perceive, `whisper` only by the listener, and both need the speaker to
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

/-- The kinds of evidence, without who said it (for naming a prior). -/
inductive EvidKind | self | seen | sensed | inferred | assumed | told | relayed | rumour
  deriving DecidableEq, Repr

def Evid.kind {C : Type} : Evid C → EvidKind
  | .self => .self | .seen => .seen | .sensed => .sensed | .inferred => .inferred
  | .assumed => .assumed | .told _ => .told | .relayed _ => .relayed | .rumour => .rumour

/-- Why a piece of evidence got the strength it did. Stored and compared as a
constructor, which the kernel decides in one step (words compared letter by
letter were the costliest part of comparing two states); `Reason.text` gives
the words, so reports and explanations read as before. `custom i` is a story's
or a module's own reason, worded by entry `i` of its `ReasonText`. -/
inductive Reason where
  | prior (k : EvidKind)
  | trustsSpeaker | distrustsSpeaker | tensionWithSpeaker
  | gullible | openMinded | skeptical | paranoid
  | custom (i : Nat)
  deriving DecidableEq, Repr

/-- The words for a story's or module's own reasons (`Reason.custom i`), by fact type. -/
class ReasonText (Φ : Type) where
  texts : List String

instance (priority := low) {Φ : Type} : ReasonText Φ := ⟨[]⟩

def EvidKind.text : EvidKind → String
  | .self => "own knowledge" | .seen => "seeing" | .sensed => "sensing" | .inferred => "inference"
  | .assumed => "assumption" | .told => "being told" | .relayed => "second-hand report"
  | .rumour => "rumour"

/-- A reason in words. -/
def Reason.text (Φ : Type) [ReasonText Φ] : Reason → String
  | .prior k => s!"prior for {k.text}"
  | .trustsSpeaker => "trusts the speaker"
  | .distrustsSpeaker => "does not trust the speaker"
  | .tensionWithSpeaker => "tension with the speaker"
  | .gullible => "gullible" | .openMinded => "open-minded"
  | .skeptical => "skeptical" | .paranoid => "paranoid"
  | .custom i => (ReasonText.texts (Φ := Φ))[i]?.getD s!"reason {i}"

structure Held (C Φ : Type) where
  b : Belief C Φ
  src : Evid C
  rank : Nat
  stamp : Nat
  up : Upgrade
  /-- the character has caught the source of this report out -/
  caught : Bool := false
  /-- story time when it was learned -/
  heard : Nat := 0
  /-- story time the information is about -/
  about : Nat := 0
  /-- why it got its strength: the prior and each adjustment, named -/
  reasons : List (Reason × Int) := []
  deriving DecidableEq, Repr

class HasMinds (W : Type) (C Φ : outParam Type) where
  beliefs : W → C → List (Held C Φ)
  setBeliefs : W → C → List (Held C Φ) → W
  /-- the world's record of the permanent conclusions `c` has drawn (L5 in
  `abstractions/ROUND-1.md`); `none`, the default, keeps no record and `view`
  rebuilds the past views instead. -/
  settled : W → C → Option (List (Φ × Bool)) := fun _ _ => none
  setSettled : W → C → List (Φ × Bool) → W := fun w _ _ => w

/-- A literal: a fact (`true`) or its denial (`false`). -/
abbrev BLit (Φ : Type) := Φ × Bool

/-- How a character weighs information; supplied by the story. -/
class Credence (W C Φ : Type) where
  /-- named adjustments to the prior strength of evidence `e` for hearer `c`,
  given what it is about (so trust can depend on the topic) -/
  reasons : W → C → Evid C → BLit Φ → List (Reason × Int)
  /-- strength at which `c` accepts information outright -/
  acceptAt : W → C → Int
  /-- `c` takes accepted information conservatively -/
  stubborn : W → C → Bool
  /-- `c` has caught `d` out -/
  onBetrayal : W → C → C → W

/-- Who can perceive at all: a story says, for instance, that the dead and
mindless puppets see nothing. Without an instance, everyone does. -/
class Perceives (W C : Type) where
  perceives : W → C → Bool

instance (priority := low) {W C : Type} : Perceives W C := ⟨fun _ _ => true⟩

instance (priority := low) {W C Φ : Type} : Credence W C Φ :=
  ⟨fun _ _ _ _ => [], fun _ _ => 3, fun _ _ => false, fun w _ _ => w⟩

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
  /-- `c` sends `d` a message saying `l` (a text, a letter): `d` learns it as testimony, nobody
  else hears it, and they need not be together -/
  | message (c d : C) (l : Φ × Bool)
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
  [HasLoc W C P] [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ] [Credence W C Φ]
  [Fluent Φ] [Clock W] [PartialLoc W C]

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

/-! Without lore, `closure` changes nothing, and a literal need only be checked
against what has been kept (which is consistent already): `admitPlain`, proved
equal to `admit`, takes quadratic time where `admit` takes cubic. -/

theorem closure_of_nil (h : Lore.rules (Φ := Φ) = []) (ls : List (BLit Φ)) : closure ls = ls := by
  simp only [closure, h, List.length_nil, Nat.zero_add]
  rfl

theorem consistent_snoc (kept : List (BLit Φ)) (l : BLit Φ) (hk : consistent kept = true) :
    consistent (kept ++ [l]) = (!clash l l && kept.all fun y => !clash l y && !clash y l) := by
  have hk' : ∀ x ∈ kept, ∀ y ∈ kept, clash x y = false := by
    simpa [consistent, List.all_eq_true] using hk
  unfold consistent
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.all_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3, fun y hy => ⟨h2 y hy, (h1 y hy).2⟩⟩
  · rintro ⟨h3, h2⟩
    exact ⟨fun x hx => ⟨hk' x hx, (h2 x hx).2⟩, fun y hy => (h2 y hy).1, h3⟩

def admitPlain (ls : List (BLit Φ)) : List (BLit Φ) :=
  ls.foldl (fun kept l => if !clash l l && kept.all (fun y => !clash l y && !clash y l)
    then kept ++ [l] else kept) []

theorem admit_eq_admitPlain (h : Lore.rules (Φ := Φ) = []) (ls : List (BLit Φ)) :
    admit ls = admitPlain ls := by
  unfold admit admitPlain
  simp only [closure_of_nil h]
  suffices ∀ kept, consistent kept = true →
      ls.foldl (fun kept l => if consistent (kept ++ [l]) then kept ++ [l] else kept) kept =
      ls.foldl (fun kept l => if !clash l l && kept.all (fun y => !clash l y && !clash y l)
        then kept ++ [l] else kept) kept from this [] rfl
  induction ls with
  | nil => intro _ _; rfl
  | cons l ls ih =>
    intro kept hk
    simp only [List.foldl_cons, consistent_snoc kept l hk]
    split
    · exact ih _ (by rw [consistent_snoc kept l hk]; assumption)
    · exact ih _ hk

private def isFluent (h : Held C Φ) : Bool :=
  match litOf h.b with | some l => Fluent.fluent l.1 | none => false

/-- Higher rank first; on a tie, a newer radical item goes first and a newer
conservative one goes last. -/
def before (x y : Held C Φ) : Bool :=
  x.rank > y.rank || (x.rank == y.rank &&
    (if x.stamp ≥ y.stamp then x.up != .conservative else y.up == .conservative))

def ordered (hs : List (Held C Φ)) : List (Held C Φ) := sortBy before hs

/-- A changeable fact is stale once newer adopted information about the same
thing contradicts it: the world may have moved on, whatever the old evidence. -/
def stale (hs : List (Held C Φ)) (h : Held C Φ) : Bool :=
  isFluent h && hs.any fun h' => isFluent h' && h'.up != .note && h'.about > h.about &&
    match litOf h.b, litOf h'.b with
    | some l, some l' => clash l l'
    | _, _ => false

/-- The items that can enter a view: first-order and not merely noted. Only
these can make another item stale, so `lits` sorts just them (the nested
beliefs witnesses add for each other are most of a base). -/
private def adoptable (hs : List (Held C Φ)) : List (Held C Φ) :=
  hs.filter fun h => h.up != .note && (litOf h.b).isSome

private def lits (hs : List (Held C Φ)) : List (BLit Φ) :=
  let hs := adoptable hs
  (ordered (hs.filter fun h => !stale hs h)).filterMap fun h => litOf h.b

/-! ## The kernel's view (`abstractions/ROUND-2.md`)

`lits` and `admitPlain` are the definition; `litsK` and `admitK` compute them,
and are what `view` runs (`litsK_eq`, `admitK_eq`). The kernel spends most of a
story's proof in views (each witness rebuilds one at every learn), and there:

* each literal is tested against every literal kept so far, and each test walks
  `Supersedes`, so `admitPlain` is quadratic in the base with a large constant.
  `admitK` keeps three bit masks over what it has kept (the `Supersedes.code` of
  each positive and each negative literal, the `cls` of each positive one). A
  literal whose bits are clear clashes with nothing kept, and the scan is
  skipped; only a literal that may clash is scanned, as before. In a story,
  that is almost only the ones the view then drops;
* `stale` asks the same question of the information that could outdate an
  item, so the same masks spare `lits` its scans;
* `before` compares with `Nat.blt`/`Nat.ble` and a match, not `decide`;
* the loops are `K` functions, which the kernel reduces by their recursors.

Masks are `Nat`s: the kernel's bit operations on literals are single steps. -/

/-- Bit `n` of `m`. -/
def bitOf (m n : Nat) : Bool := Nat.beq ((m >>> n) % 2) 1

/-- `m` with bit `n` set. -/
def addBit (m n : Nat) : Nat := m ||| (1 <<< n)

theorem nbeq_eq (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq_true_eq])

theorem nblt_eq (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.blt_eq])

theorem nble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq])

theorem bitOf_eq_testBit (m n : Nat) : bitOf m n = m.testBit n := by
  rw [bitOf, nbeq_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]

theorem bitOf_addBit (m n k : Nat) : bitOf (addBit m n) k = (bitOf m k || decide (n = k)) := by
  simp only [bitOf_eq_testBit, addBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- What a set of literals has, as bits: the codes of its positive and its negative
literals, and the classes of its positive ones. -/
structure Masks where
  pos : Nat := 0
  neg : Nat := 0
  cls : Nat := 0

def Masks.add (m : Masks) (l : BLit Φ) : Masks :=
  if l.2 then
    { m with pos := addBit m.pos (Supersedes.code l.1),
             cls := let c := Supersedes.cls l.1; if Nat.beq c 0 then m.cls else addBit m.cls c }
  else { m with neg := addBit m.neg (Supersedes.code l.1) }

/-- `l` may clash with a literal the masks have: some bit `l` would clash with is set. -/
def Masks.maybe (m : Masks) (l : BLit Φ) : Bool :=
  if l.2 then bitOf m.neg (Supersedes.code l.1) ||
    (let c := Supersedes.cls l.1; !Nat.beq c 0 && bitOf m.cls c)
  else bitOf m.pos (Supersedes.code l.1)

/-- The masks have every literal of `L`. -/
def Masks.Has (m : Masks) (L : List (BLit Φ)) : Prop :=
  ∀ y ∈ L, (y.2 = true → bitOf m.pos (Supersedes.code y.1) = true ∧
      (Supersedes.cls y.1 ≠ 0 → bitOf m.cls (Supersedes.cls y.1) = true)) ∧
    (y.2 = false → bitOf m.neg (Supersedes.code y.1) = true)

theorem Masks.has_nil (m : Masks) : m.Has ([] : List (BLit Φ)) := fun _ h => nomatch h

theorem Masks.has_add {m : Masks} {L : List (BLit Φ)} (h : m.Has L) (l : BLit Φ) :
    (m.add l).Has (L ++ [l]) := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨h1, h2⟩ := h y hy
    unfold Masks.add
    split
    · refine ⟨fun hp => ⟨?_, fun hc => ?_⟩, fun hn => h2 hn⟩
      · simp [bitOf_addBit, (h1 hp).1]
      · simp only []
        split <;> simp [bitOf_addBit, (h1 hp).2 hc]
    · exact ⟨fun hp => h1 hp, fun hn => by simp [bitOf_addBit, h2 hn]⟩
  · obtain rfl := List.mem_singleton.mp hy
    unfold Masks.add
    split
    · rename_i hp
      refine ⟨fun _ => ⟨by simp [bitOf_addBit], fun hc => ?_⟩, fun hn => by simp_all⟩
      simp only []
      have : Nat.beq (Supersedes.cls y.1) 0 = false := by rw [nbeq_eq]; simpa using hc
      rw [this]; simp [bitOf_addBit]
    · rename_i hp
      exact ⟨fun h => absurd h hp, fun _ => by simp [bitOf_addBit]⟩

/-- Every bit the masks have set is a literal of `L`. -/
def Masks.Sound (m : Masks) (L : List (BLit Φ)) : Prop :=
  ∀ k, (bitOf m.pos k = true → ∃ y ∈ L, y.2 = true ∧ Supersedes.code y.1 = k) ∧
    (bitOf m.neg k = true → ∃ y ∈ L, y.2 = false ∧ Supersedes.code y.1 = k)

/-- The masks of exactly `L`'s literals. -/
def Masks.Ok (m : Masks) (L : List (BLit Φ)) : Prop := m.Has L ∧ m.Sound L

theorem bitOf_zero (k : Nat) : bitOf 0 k = false := by
  rw [bitOf_eq_testBit]; exact Nat.zero_testBit k

theorem Masks.ok_nil : ({} : Masks).Ok ([] : List (BLit Φ)) :=
  ⟨Masks.has_nil _, fun k => ⟨fun h => by simp [bitOf_zero] at h, fun h => by simp [bitOf_zero] at h⟩⟩

theorem Masks.ok_add {m : Masks} {L : List (BLit Φ)} (h : m.Ok L) (l : BLit Φ) :
    (m.add l).Ok (L ++ [l]) := by
  refine ⟨Masks.has_add h.1 l, fun k => ?_⟩
  obtain ⟨hp, hn⟩ := h.2 k
  have up : ∀ y, y ∈ L → y ∈ L ++ [l] := fun y hy => List.mem_append_left _ hy
  unfold Masks.add
  obtain ⟨φ, b⟩ := l
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, bitOf_addBit, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨y, hy, h1, h2⟩ := hp h; exact ⟨y, up y hy, h1, h2⟩
    · rcases h with h | h
      · obtain ⟨y, hy, h1, h2⟩ := hn h; exact ⟨y, up y hy, h1, h2⟩
      · exact ⟨(φ, false), by simp, rfl, h⟩
  · simp only [↓reduceIte, bitOf_addBit, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · obtain ⟨y, hy, h1, h2⟩ := hp h; exact ⟨y, up y hy, h1, h2⟩
      · exact ⟨(φ, true), by simp, rfl, h⟩
    · obtain ⟨y, hy, h1, h2⟩ := hn h; exact ⟨y, up y hy, h1, h2⟩

/-- A literal that clashes with one the masks have has a bit set. -/
theorem Masks.maybe_of_clash {m : Masks} {L : List (BLit Φ)} (h : m.Has L) (l y : BLit Φ)
    (hy : y ∈ L) (hc : clash l y = true ∨ clash y l = true) : m.maybe l = true := by
  obtain ⟨h1, h2⟩ := h y hy
  obtain ⟨φ, b⟩ := l
  obtain ⟨ψ, b'⟩ := y
  have hsup : ∀ x z : Φ, Supersedes.supersedes x z = true →
      Supersedes.cls x = Supersedes.cls z ∧ Supersedes.cls x ≠ 0 := Supersedes.cls_sup
  unfold Masks.maybe
  unfold clash at hc
  cases b <;> cases b' <;> simp [nbeq_eq] at hc h1 h2 ⊢
  · rcases hc with rfl | rfl <;> exact h1.1
  · rcases hc with rfl | rfl <;> simp [h2]
  · right
    rcases hc with ⟨_, hs⟩ | ⟨_, hs⟩
    · obtain ⟨hc, h0⟩ := hsup φ ψ hs
      exact ⟨h0, hc ▸ h1.2 (hc ▸ h0)⟩
    · obtain ⟨hc, h0⟩ := hsup ψ φ hs
      exact ⟨hc ▸ h0, hc ▸ h1.2 h0⟩

/-- A literal whose bits are clear clashes with nothing the masks have. -/
theorem Masks.no_clash {m : Masks} {L : List (BLit Φ)} (h : m.Has L) (l : BLit Φ)
    (hm : m.maybe l = false) : ∀ y ∈ L, clash l y = false ∧ clash y l = false := by
  intro y hy
  refine ⟨?_, ?_⟩
  · cases hc : clash l y
    · rfl
    · have := Masks.maybe_of_clash h l y hy (Or.inl hc); rw [hm] at this; exact absurd this (by decide)
  · cases hc : clash y l
    · rfl
    · have := Masks.maybe_of_clash h l y hy (Or.inr hc); rw [hm] at this; exact absurd this (by decide)

/-- One step of `admitK`: what has been kept, and its masks. -/
def admitKStep (st : List (BLit Φ) × Masks) (l : BLit Φ) : List (BLit Φ) × Masks :=
  if st.2.maybe l && !(K.all st.1 fun y => !clash l y && !clash y l) then st
  else (K.append st.1 [l], st.2.add l)

/-- `admitPlain`, deciding most literals by bit tests (`admitK_eq`). -/
def admitK (ls : List (BLit Φ)) : List (BLit Φ) :=
  (K.foldl admitKStep ([], {}) ls).1

theorem clash_self (l : BLit Φ) : clash l l = false := by
  unfold clash; simp

theorem admitKStep_spec (st : List (BLit Φ) × Masks) (hst : st.2.Has st.1) (l : BLit Φ) :
    (admitKStep st l).1 = (if !clash l l && st.1.all (fun y => !clash l y && !clash y l)
      then st.1 ++ [l] else st.1) ∧ (admitKStep st l).2.Has (admitKStep st l).1 := by
  unfold admitKStep
  rw [K.all_eq, K.append_eq, clash_self]
  cases hm : st.2.maybe l
  · have hall : (st.1.all fun y => !clash l y && !clash y l) = true := by
      rw [List.all_eq_true]
      intro y hy
      obtain ⟨h1, h2⟩ := Masks.no_clash hst l hm y hy
      simp [h1, h2]
    simp only [hall, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
    exact ⟨by first | rfl | trivial, Masks.has_add hst l⟩
  · cases hall : (st.1.all fun y => !clash l y && !clash y l)
    · simp only [Bool.not_false, Bool.and_self, ↓reduceIte, Bool.and_false, Bool.false_eq_true]
      exact ⟨by first | rfl | trivial, hst⟩
    · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.and_self]
      exact ⟨by first | rfl | trivial, Masks.has_add hst l⟩

theorem admitK_eq (ls : List (BLit Φ)) : admitK ls = admitPlain ls := by
  unfold admitK admitPlain
  rw [K.foldl_eq]
  suffices ∀ st : List (BLit Φ) × Masks, st.2.Has st.1 →
      (ls.foldl admitKStep st).1 = ls.foldl (fun kept l => if !clash l l && kept.all
        (fun y => !clash l y && !clash y l) then kept ++ [l] else kept) st.1 from
    this ([], {}) (Masks.has_nil _)
  induction ls with
  | nil => intro _ _; rfl
  | cons l ls ih =>
    intro st hst
    obtain ⟨e, hh⟩ := admitKStep_spec st hst l
    simp only [List.foldl_cons]
    rw [ih _ hh, e]

/-! ### The lore's closure is a least fixpoint, and `admit` with lore

`closure` runs `|rules| + 1` passes of the lore. A pass that changes the list adds
the head of a rule whose head was missing, so the passes run out of changes before
they run out, and the list `closure` returns is closed under the rules
(`closure_closed`). So what it contains is what the lore derives from what its
argument contains (`mem_closure`), and `consistent (closure (kept ++ [l]))`, the
test `admit` runs at every literal, depends only on that. `admitL` keeps the
closure of what it has kept, with its masks, and checks only what a literal adds
to it (`admitL_eq`). -/

/-- `x` follows from `ls` by the lore. -/
inductive Derivable (ls : List (BLit Φ)) : BLit Φ → Prop
  | base {x : BLit Φ} : x ∈ ls → Derivable ls x
  | rule (r : LoreRule Φ) : r ∈ Lore.rules (Φ := Φ) → (∀ b ∈ r.body, Derivable ls b) →
      Derivable ls r.head

/-- One pass of the lore (the `step` of `closure`). -/
def closureStep (ls : List (BLit Φ)) : List (BLit Φ) :=
  (Lore.rules (Φ := Φ)).foldl (fun acc r =>
    if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) ls

theorem closure_eq_go (ls : List (BLit Φ)) :
    closure ls = closure.go closureStep ((Lore.rules (Φ := Φ)).length + 1) ls := rfl

private theorem foldl_step_prefix (rs : List (LoreRule Φ)) (acc : List (BLit Φ)) :
    ∃ X, rs.foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) acc = acc ++ X := by
  induction rs generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons r rs ih =>
    simp only [List.foldl_cons]
    split
    · obtain ⟨X, hX⟩ := ih (acc ++ [r.head]); exact ⟨[r.head] ++ X, by simp [hX]⟩
    · exact ih acc

theorem closureStep_prefix (ls : List (BLit Φ)) : ∃ X, closureStep ls = ls ++ X :=
  foldl_step_prefix _ ls

theorem closure_go_prefix (f : List (BLit Φ) → List (BLit Φ)) (hf : ∀ l, ∃ X, f l = l ++ X) :
    ∀ n ls, ∃ X, closure.go f n ls = ls ++ X
  | 0, ls => ⟨[], by simp [closure.go]⟩
  | n + 1, ls => by
    obtain ⟨X, hX⟩ := hf ls
    obtain ⟨Y, hY⟩ := closure_go_prefix f hf n (f ls)
    refine ⟨X ++ Y, ?_⟩
    show closure.go f n (f ls) = _
    rw [hY, hX, List.append_assoc]

theorem closure_prefix (ls : List (BLit Φ)) : ∃ X, closure ls = ls ++ X :=
  closure_go_prefix _ closureStep_prefix _ _

private theorem foldl_step_sound (L : List (BLit Φ)) (rs : List (LoreRule Φ))
    (hrs : ∀ r ∈ rs, r ∈ Lore.rules (Φ := Φ)) (acc : List (BLit Φ)) (hacc : ∀ y ∈ acc, Derivable L y) :
    ∀ y ∈ rs.foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) acc,
      Derivable L y := by
  induction rs generalizing acc with
  | nil => simpa using hacc
  | cons r rs ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hfire
      apply ih (fun r' h => hrs r' (List.mem_cons_of_mem _ h))
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hacc y hy
      · obtain rfl := List.mem_singleton.mp hy
        simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hfire
        exact .rule r (hrs r List.mem_cons_self) fun b hb => hacc b (hfire.1 b hb)
    · exact ih (fun r' h => hrs r' (List.mem_cons_of_mem _ h)) acc hacc

theorem mem_closure_sound (ls : List (BLit Φ)) : ∀ y ∈ closure ls, Derivable ls y := by
  rw [closure_eq_go]
  suffices ∀ n acc, (∀ y ∈ acc, Derivable ls y) → ∀ y ∈ closure.go closureStep n acc, Derivable ls y from
    this _ ls fun y hy => .base hy
  intro n
  induction n with
  | zero => intro acc h; simpa [closure.go] using h
  | succ n ih =>
    intro acc h
    exact ih _ (foldl_step_sound ls _ (fun r h => h) acc h)

/-- Rules whose head the list lacks. -/
private def missing (L : List (BLit Φ)) : Nat :=
  ((Lore.rules (Φ := Φ)).filter fun r => !L.contains r.head).length

private theorem length_filter_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ rs : List α, (∀ r ∈ rs, q r = true → p r = true) → (rs.filter q).length ≤ (rs.filter p).length
  | [], _ => by simp
  | r :: rs, h => by
    have ih := length_filter_le_of_imp p q rs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hr := h r List.mem_cons_self
    cases hq : q r <;> cases hp : p r <;> simp only [List.filter_cons, hq, hp, Bool.false_eq_true,
      ↓reduceIte, List.length_cons] <;> first | omega | exact absurd (hr hq) (by simp [hp])

private theorem length_filter_lt {α : Type} (p q : α → Bool) :
    ∀ rs : List α, (∀ r ∈ rs, q r = true → p r = true) → (∃ r ∈ rs, p r = true ∧ q r = false) →
      (rs.filter q).length < (rs.filter p).length
  | [], _, ⟨_, h, _⟩ => nomatch h
  | r :: rs, hqp, ⟨r', hr', hp', hq'⟩ => by
    have hqp' : ∀ x ∈ rs, q x = true → p x = true := fun x h => hqp x (List.mem_cons_of_mem _ h)
    have hle := length_filter_le_of_imp p q rs hqp'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · simp only [List.filter_cons, hp', hq', Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    · have ih := length_filter_lt p q rs hqp' ⟨r', hr', hp', hq'⟩
      have hr := hqp r List.mem_cons_self
      cases hq : q r <;> cases hp : p r <;> simp only [List.filter_cons, hq, hp, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] <;> first | omega | exact absurd (hr hq) (by simp [hp])

private theorem foldl_step_change (rs : List (LoreRule Φ)) (acc : List (BLit Φ)) :
    rs.foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) acc = acc ∨
    ∃ r ∈ rs, r.head ∉ acc ∧ r.head ∈ rs.foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) acc := by
  induction rs generalizing acc with
  | nil => exact .inl rfl
  | cons r rs ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hfire
      right
      refine ⟨r, List.mem_cons_self, ?_, ?_⟩
      · have h2 : acc.contains r.head = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfire; exact hfire.2
        intro hm
        rw [List.contains_iff_mem.mpr hm] at h2; exact absurd h2 (by decide)
      · obtain ⟨X, hX⟩ := foldl_step_prefix rs (acc ++ [r.head])
        rw [hX]; simp
    · rcases ih acc with h | ⟨r', hr', h1, h2⟩
      · exact .inl h
      · exact .inr ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩

private theorem closureStep_progress (L : List (BLit Φ)) :
    closureStep L = L ∨ missing (closureStep L) < missing L := by
  rcases foldl_step_change (Lore.rules (Φ := Φ)) L with h | ⟨r, hr, h1, h2⟩
  · exact .inl h
  · right
    obtain ⟨X, hX⟩ := closureStep_prefix L
    unfold missing
    apply length_filter_lt
    · intro r' _ hq
      simp only [Bool.not_eq_true'] at hq ⊢
      cases hc : L.contains r'.head
      · rfl
      · have : (closureStep L).contains r'.head = true := by
          rw [hX]; simp only [List.contains_append, hc, Bool.true_or]
        rw [this] at hq; exact absurd hq (by decide)
    · refine ⟨r, hr, ?_, ?_⟩
      · simpa using h1
      · have : r.head ∈ closureStep L := h2
        simpa using this

/-- Closed under the lore. -/
def LoreClosed (L : List (BLit Φ)) : Prop :=
  ∀ r ∈ Lore.rules (Φ := Φ), (∀ b ∈ r.body, b ∈ L) → r.head ∈ L

private theorem foldl_step_fixed (rs : List (LoreRule Φ)) (acc : List (BLit Φ))
    (h : rs.foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) acc = acc) :
    ∀ r ∈ rs, (∀ b ∈ r.body, b ∈ acc) → r.head ∈ acc := by
  induction rs generalizing acc with
  | nil => intro r hr; nomatch hr
  | cons r rs ih =>
    simp only [List.foldl_cons] at h
    split at h
    · obtain ⟨X, hX⟩ := foldl_step_prefix rs (acc ++ [r.head])
      rw [hX] at h
      have := congrArg List.length h
      simp at this
    · rename_i hnot
      intro r' hr' hb
      rcases List.mem_cons.mp hr' with rfl | hr'
      · cases hc : acc.contains r'.head
        · exfalso
          apply hnot
          simp only [Bool.and_eq_true, List.all_eq_true, hc, Bool.not_false, and_true]
          exact fun b hb' => List.contains_iff_mem.mpr (hb b hb')
        · exact List.contains_iff_mem.mp hc
      · exact ih acc h r' hr' hb

private theorem closure_go_fixed (L : List (BLit Φ)) (h : closureStep L = L) :
    ∀ n, closure.go closureStep n L = L
  | 0 => rfl
  | n + 1 => by simp only [closure.go, h]; exact closure_go_fixed L h n

private theorem closure_go_closed : ∀ n (L : List (BLit Φ)), missing L < n →
    LoreClosed (closure.go closureStep n L)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, L, h => by
    simp only [closure.go]
    rcases closureStep_progress L with he | hlt
    · rw [he, closure_go_fixed L he]
      exact foldl_step_fixed _ L he
    · exact closure_go_closed n _ (by omega)

theorem closure_closed (ls : List (BLit Φ)) : LoreClosed (closure ls) := by
  rw [closure_eq_go]
  exact closure_go_closed _ _ (Nat.lt_succ_of_le (List.length_filter_le _ _))

theorem mem_closure (ls : List (BLit Φ)) (x : BLit Φ) : x ∈ closure ls ↔ Derivable ls x := by
  constructor
  · exact mem_closure_sound ls x
  · intro h
    induction h with
    | base hx =>
      obtain ⟨X, hX⟩ := closure_prefix ls
      rw [hX]; exact List.mem_append_left _ hx
    | rule r hr _ ih => exact closure_closed ls r hr ih

theorem Derivable.mono {A B : List (BLit Φ)} (h : ∀ y ∈ A, Derivable B y) {x : BLit Φ}
    (hx : Derivable A x) : Derivable B x := by
  induction hx with
  | base hy => exact h _ hy
  | rule r hr _ ih => exact .rule r hr ih

theorem consistent_congr {A B : List (BLit Φ)} (h : ∀ x, x ∈ A ↔ x ∈ B) :
    consistent A = consistent B := by
  apply Bool.eq_iff_iff.mpr
  simp only [consistent, List.all_eq_true, h]

/-- What a closure adds to a consistent list need only be checked against it and itself. -/
theorem consistent_append (C N : List (BLit Φ)) (hC : consistent C = true) :
    consistent (C ++ N) = N.all fun x => (C ++ N).all fun y => !clash x y && !clash y x := by
  have hC' : ∀ x ∈ C, ∀ y ∈ C, clash x y = false := by
    simpa [consistent, List.all_eq_true] using hC
  apply Bool.eq_iff_iff.mpr
  simp only [consistent, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.mem_append]
  constructor
  · intro h x hx y hy
    exact ⟨h x (.inr hx) y hy, h y hy x (.inr hx)⟩
  · intro h x hx y hy
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact hC' x hx y hy
      · exact (h y hy x (.inl hx)).2
    · exact (h x hx y hy).1

/-- `l ∈ L` as the masks see it: a clear bit means absent (`containsK_eq`). -/
def containsK (m : Masks) (L : List (BLit Φ)) (x : BLit Φ) : Bool :=
  (if x.2 then bitOf m.pos (Supersedes.code x.1) else bitOf m.neg (Supersedes.code x.1)) &&
    (Supersedes.codeInj (Φ := Φ) || L.contains x)

theorem containsK_eq {m : Masks} {L : List (BLit Φ)} (h : m.Ok L) (x : BLit Φ) :
    containsK m L x = L.contains x := by
  unfold containsK
  cases hc : L.contains x
  · simp only [Bool.or_false]
    cases hi : Supersedes.codeInj (Φ := Φ)
    · simp
    · -- an injective code: a set bit is a literal of `L` with that very fact
      obtain ⟨φ, b⟩ := x
      cases b
      · cases hb : bitOf m.neg (Supersedes.code φ)
        · rfl
        · obtain ⟨y, hy, h1, h2⟩ := (h.2 _).2 hb
          have := Supersedes.code_inj hi _ _ h2
          obtain ⟨ψ, b'⟩ := y
          simp only [] at h1 this; subst h1; subst this
          rw [List.contains_iff_mem.mpr hy] at hc; exact absurd hc (by decide)
      · cases hb : bitOf m.pos (Supersedes.code φ)
        · rfl
        · obtain ⟨y, hy, h1, h2⟩ := (h.2 _).1 hb
          have := Supersedes.code_inj hi _ _ h2
          obtain ⟨ψ, b'⟩ := y
          simp only [] at h1 this; subst h1; subst this
          rw [List.contains_iff_mem.mpr hy] at hc; exact absurd hc (by decide)
  · have hx := (h.1 x (List.contains_iff_mem.mp hc))
    obtain ⟨φ, b⟩ := x
    cases b <;> simp_all

/-- One rule of a pass, with the masks of what has been derived and whether a rule fired. -/
def closureRuleK (st : List (BLit Φ) × Masks × Bool) (r : LoreRule Φ) : List (BLit Φ) × Masks × Bool :=
  if K.all r.body (containsK st.2.1 st.1) && !containsK st.2.1 st.1 r.head
  then (K.append st.1 [r.head], st.2.1.add r.head, true) else st

/-- One pass of the lore, with the masks of what has been derived; `true` if a rule fired. -/
def closureStepK (st : List (BLit Φ) × Masks) : List (BLit Φ) × Masks × Bool :=
  K.foldl closureRuleK (st.1, st.2, false) (Lore.rules (Φ := Φ))

private theorem closureRuleK_spec (st : List (BLit Φ) × Masks × Bool) (h : st.2.1.Ok st.1) (r : LoreRule Φ) :
    (closureRuleK st r).1 = (if r.body.all st.1.contains && !st.1.contains r.head then
      st.1 ++ [r.head] else st.1) ∧ (closureRuleK st r).2.1.Ok (closureRuleK st r).1 ∧
      ((closureRuleK st r).2.2 = false → st.2.2 = false ∧ (closureRuleK st r).1 = st.1) := by
  unfold closureRuleK
  rw [K.all_eq, K.append_eq]
  have hb : (r.body.all (containsK st.2.1 st.1)) = r.body.all st.1.contains := by
    congr 1; funext x; exact containsK_eq h x
  rw [hb, containsK_eq h]
  split
  · exact ⟨rfl, Masks.ok_add h r.head, fun h => nomatch h⟩
  · exact ⟨rfl, h, fun h => ⟨h, rfl⟩⟩

private theorem closureStepK_go (rs : List (LoreRule Φ)) : ∀ st : List (BLit Φ) × Masks × Bool,
    st.2.1.Ok st.1 →
    (rs.foldl closureRuleK st).1 = rs.foldl (fun acc r =>
      if r.body.all acc.contains && !acc.contains r.head then acc ++ [r.head] else acc) st.1 ∧
    (rs.foldl closureRuleK st).2.1.Ok (rs.foldl closureRuleK st).1 ∧
    ((rs.foldl closureRuleK st).2.2 = false → st.2.2 = false ∧ (rs.foldl closureRuleK st).1 = st.1) := by
  induction rs with
  | nil => intro st h; exact ⟨rfl, h, fun h => ⟨h, rfl⟩⟩
  | cons r rs ih =>
    intro st h
    simp only [List.foldl_cons]
    obtain ⟨e1, h1, f1⟩ := closureRuleK_spec st h r
    obtain ⟨e2, h2, f2⟩ := ih _ h1
    rw [e1] at e2
    refine ⟨e2, h2, fun hf => ?_⟩
    obtain ⟨hf1, hl⟩ := f2 hf
    obtain ⟨hf0, hl0⟩ := f1 hf1
    exact ⟨hf0, hl.trans hl0⟩

theorem closureStepK_eq (st : List (BLit Φ) × Masks) (h : st.2.Ok st.1) :
    (closureStepK st).1 = closureStep st.1 ∧ (closureStepK st).2.1.Ok (closureStepK st).1 ∧
      ((closureStepK st).2.2 = false → closureStep st.1 = st.1) := by
  unfold closureStepK
  rw [K.foldl_eq]
  obtain ⟨e, hh, hf⟩ := closureStepK_go (Lore.rules (Φ := Φ)) (st.1, st.2, false) h
  refine ⟨e, hh, fun hb => ?_⟩
  have h2 := (hf hb).2
  calc closureStep st.1 = (List.foldl closureRuleK (st.1, st.2, false) Lore.rules).1 := e.symm
    _ = st.1 := h2

/-- `closure.go`, with masks, stopping at the first pass that changes nothing (the
rest would change nothing either: `closure_go_fixed`). -/
def closureGoK : Nat → List (BLit Φ) × Masks → List (BLit Φ) × Masks
  | 0, st => st
  | n + 1, st =>
    let r := closureStepK st
    if r.2.2 then closureGoK n (r.1, r.2.1) else (r.1, r.2.1)

theorem closureGoK_eq : ∀ n (st : List (BLit Φ) × Masks), st.2.Ok st.1 →
    (closureGoK n st).1 = closure.go closureStep n st.1 ∧ (closureGoK n st).2.Ok (closureGoK n st).1
  | 0, _, h => ⟨rfl, h⟩
  | n + 1, st, h => by
    obtain ⟨e, h', hf⟩ := closureStepK_eq st h
    simp only [closureGoK, closure.go]
    split
    · have := closureGoK_eq n ((closureStepK st).1, (closureStepK st).2.1) h'
      exact ⟨this.1.trans (by rw [e]), this.2⟩
    · rename_i hb
      simp only [Bool.not_eq_true] at hb
      have hfix := hf hb
      refine ⟨?_, h'⟩
      simp only []
      rw [e, hfix, closure_go_fixed _ hfix]

/-- The masks of a list. -/
def masksOf (L : List (BLit Φ)) : Masks := K.foldl Masks.add {} L

theorem masksOf_ok (L : List (BLit Φ)) : (masksOf L).Ok L := by
  unfold masksOf
  rw [K.foldl_eq]
  suffices ∀ (m : Masks) (A : List (BLit Φ)), m.Ok A → (L.foldl Masks.add m).Ok (A ++ L) by
    simpa using this {} [] Masks.ok_nil
  induction L with
  | nil => intro m A h; simpa using h
  | cons x L ih =>
    intro m A h
    simpa using ih (m.add x) (A ++ [x]) (Masks.ok_add h x)

/-- `closure`, testing membership by masks first (`closureK_eq`). -/
def closureK (ls : List (BLit Φ)) : List (BLit Φ) :=
  (closureGoK ((Lore.rules (Φ := Φ)).length + 1) (ls, masksOf ls)).1

theorem closureK_eq (ls : List (BLit Φ)) : closureK ls = closure ls := by
  unfold closureK
  rw [(closureGoK_eq _ _ (masksOf_ok ls)).1]; rfl

/-- One step of `admitL`: what has been kept, its closure, and the closure's masks. -/
def admitLStep (st : List (BLit Φ) × List (BLit Φ) × Masks) (l : BLit Φ) :
    List (BLit Φ) × List (BLit Φ) × Masks :=
  let C := st.2.1
  let m := st.2.2
  let r := closureGoK ((Lore.rules (Φ := Φ)).length + 1) (K.append C [l], m.add l)
  let N := r.1.drop C.length
  if K.all N (fun x => (!m.maybe x || K.all C fun y => !clash x y && !clash y x) &&
      K.all N fun y => !clash x y && !clash y x)
  then (K.append st.1 [l], r.1, r.2) else st

/-- `admit`: the greedy consistent prefix under the lore, checking each literal by what
it adds to the closure so far (`admitL_eq`). -/
def admitL (ls : List (BLit Φ)) : List (BLit Φ) :=
  let C₀ := closureK []
  if consistent C₀ then (K.foldl admitLStep ([], C₀, masksOf C₀) ls).1 else []

private theorem consistent_mono {A B : List (BLit Φ)} (h : ∀ x ∈ A, x ∈ B) (hB : consistent B = true) :
    consistent A = true := by
  simp only [consistent, List.all_eq_true, Bool.not_eq_true'] at hB ⊢
  exact fun x hx y hy => hB x (h x hx) y (h y hy)

theorem admit_nil_of_inconsistent (h : consistent (closure ([] : List (BLit Φ))) = false)
    (ls : List (BLit Φ)) : admit ls = [] := by
  unfold admit
  suffices ∀ ls : List (BLit Φ), ls.foldl (fun kept l =>
      if consistent (closure (kept ++ [l])) then kept ++ [l] else kept) [] = [] from this ls
  intro ls
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldl_cons, List.nil_append]
    have : consistent (closure [l]) = false := by
      cases hc : consistent (closure [l])
      · rfl
      · have := consistent_mono (A := closure []) (B := closure [l]) (fun x hx => by
          rw [mem_closure] at hx ⊢
          exact Derivable.mono (fun y hy => by simp at hy) hx) hc
        rw [h] at this; exact absurd this (by decide)
    rw [this]; exact ih

/-- What `admitLStep` keeps: its closure has what the lore derives from what was kept. -/
private def LInv (st : List (BLit Φ) × List (BLit Φ) × Masks) : Prop :=
  (∀ y, y ∈ st.2.1 ↔ Derivable st.1 y) ∧ consistent st.2.1 = true ∧ st.2.2.Ok st.2.1

private theorem admitLStep_spec (st : List (BLit Φ) × List (BLit Φ) × Masks) (hst : LInv st)
    (l : BLit Φ) : (admitLStep st l).1 =
      (if consistent (closure (st.1 ++ [l])) then st.1 ++ [l] else st.1) ∧ LInv (admitLStep st l) := by
  obtain ⟨kept, C, m⟩ := st
  obtain ⟨hmem, hcon, hhas⟩ := hst
  simp only [] at hmem hcon hhas
  unfold admitLStep
  simp only []
  rw [K.append_eq]
  obtain ⟨e, hr⟩ := closureGoK_eq ((Lore.rules (Φ := Φ)).length + 1) (C ++ [l], m.add l)
    (Masks.ok_add hhas l)
  generalize hR : closureGoK ((Lore.rules (Φ := Φ)).length + 1) (C ++ [l], m.add l) = R at e hr
  simp only [] at e
  rw [← closure_eq_go] at e
  -- the closure of `C ++ [l]` has what the closure of `kept ++ [l]` has
  have hsame : ∀ x, x ∈ closure (C ++ [l]) ↔ x ∈ closure (kept ++ [l]) := by
    intro x
    rw [mem_closure, mem_closure]
    constructor
    · exact Derivable.mono fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact Derivable.mono (fun z hz => .base (List.mem_append_left _ hz)) ((hmem y).mp hy)
        · exact .base (List.mem_append_right _ hy)
    · exact Derivable.mono fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact .base (List.mem_append_left _ ((hmem y).mpr (.base hy)))
        · exact .base (List.mem_append_right _ hy)
  obtain ⟨X, hX⟩ := closure_prefix (C ++ [l])
  have hsplit : R.1 = C ++ R.1.drop C.length := by
    rw [e, hX]; simp
  generalize hN : R.1.drop C.length = N at hsplit
  have hcons : consistent (closure (kept ++ [l])) =
      N.all fun x => (C ++ N).all fun y => !clash x y && !clash y x := by
    rw [← consistent_congr hsame, ← e, hsplit, consistent_append _ _ hcon]
  -- the test, by masks against `C` and by scanning what is new
  have htest : (K.all N fun x => (!m.maybe x || K.all C fun y => !clash x y && !clash y x) &&
      K.all N fun y => !clash x y && !clash y x) = consistent (closure (kept ++ [l])) := by
    rw [hcons]
    simp only [K.all_eq]
    congr 1; funext x
    rw [List.all_append]
    congr 1
    cases hm : m.maybe x
    · simp only [Bool.not_false, Bool.true_or]
      symm; rw [List.all_eq_true]
      intro y hy
      obtain ⟨h1, h2⟩ := Masks.no_clash hhas.1 x hm y hy
      simp [h1, h2]
    · simp
  rw [htest]
  cases hc : consistent (closure (kept ++ [l]))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by first | rfl | trivial, hmem, hcon, hhas⟩
  · simp only [↓reduceIte]
    refine ⟨by first | rfl | trivial, fun y => ?_, ?_, hr⟩
    · rw [e, hsame, mem_closure]; try exact Iff.rfl
    · rw [e, consistent_congr hsame, hc]

theorem admitL_eq (ls : List (BLit Φ)) : admitL ls = admit ls := by
  unfold admitL
  simp only [closureK_eq]
  split
  · rename_i h0
    rw [K.foldl_eq]
    unfold admit
    suffices ∀ st : List (BLit Φ) × List (BLit Φ) × Masks, LInv st →
        (ls.foldl admitLStep st).1 = ls.foldl (fun kept l =>
          if consistent (closure (kept ++ [l])) then kept ++ [l] else kept) st.1 from
      this _ ⟨fun y => by rw [mem_closure], h0, masksOf_ok _⟩
    induction ls with
    | nil => intro _ _; rfl
    | cons l ls ih =>
      intro st hst
      obtain ⟨e, hh⟩ := admitLStep_spec st hst l
      simp only [List.foldl_cons]
      rw [ih _ hh, e]
  · rename_i h0
    simp only [Bool.not_eq_true] at h0
    exact (admit_nil_of_inconsistent h0 ls).symm

private def isCons : Upgrade → Bool
  | .conservative => true
  | _ => false

/-- `before`, by `Nat.blt`/`Nat.ble` and a match (`beforeK_eq`). -/
def beforeK (x y : Held C Φ) : Bool :=
  Nat.blt y.rank x.rank || (Nat.beq x.rank y.rank &&
    (if Nat.ble y.stamp x.stamp then !isCons x.up else isCons y.up))

theorem beforeK_eq : (beforeK : Held C Φ → Held C Φ → Bool) = before := by
  funext x y
  unfold beforeK before
  have e : (x.rank == y.rank) = decide (x.rank = y.rank) := Bool.eq_iff_iff.mpr (by simp)
  rw [nblt_eq, nble_eq, nbeq_eq, e]
  have u : ∀ u : Upgrade, (u != .conservative) = !isCons u ∧ (u == .conservative) = isCons u := by
    intro u; cases u <;> decide
  simp only [(u x.up).1, (u y.up).2]
  by_cases h3 : y.stamp ≤ x.stamp <;> simp [h3]

/-- The masks of the items that can outdate others (`stale`): fluent and adopted. -/
private def staleMasks (A : List (Held C Φ)) : Masks :=
  K.foldl (fun m h => if isFluent h && h.up != .note then
    (match litOf h.b with | some l => m.add l | none => m) else m) {} A

/-- `stale`, over the items that can outdate others (fluent, adopted), comparing times
first (`staleK_eq`). -/
def staleK (cands : List (Held C Φ)) (h : Held C Φ) : Bool :=
  K.any cands fun h' => Nat.blt h.about h'.about &&
    match litOf h.b, litOf h'.b with
    | some l, some l' => clash l l'
    | _, _ => false

theorem staleK_eq (A : List (Held C Φ)) (h : Held C Φ) (hf : isFluent h = true) :
    staleK (A.filter fun h => isFluent h && h.up != .note) h = stale A h := by
  unfold staleK stale
  rw [K.any_eq, hf, List.any_filter, Bool.true_and]
  congr 1; funext h'
  rw [nblt_eq]
  cases isFluent h' <;> cases (h'.up != Upgrade.note) <;> simp [Bool.and_assoc]

/-- `lits`, sparing `stale`'s scan where the masks show nothing could outdate an item (`litsK_eq`). -/
def litsK (hs : List (Held C Φ)) : List (BLit Φ) :=
  let A := K.filter (fun h => h.up != .note && (litOf h.b).isSome) hs
  let m := staleMasks A
  let cands := K.filter (fun h => isFluent h && h.up != .note) A
  K.filterMap (fun h => litOf h.b) (K.sortBy beforeK (K.filter (fun h =>
    !(isFluent h && (match litOf h.b with | some l => m.maybe l | none => false) && staleK cands h)) A))

private theorem staleMasks_has (A : List (Held C Φ)) :
    (staleMasks A).Has ((A.filter fun h => isFluent h && h.up != .note).filterMap fun h => litOf h.b) := by
  unfold staleMasks
  rw [K.foldl_eq]
  suffices ∀ (m : Masks) (L : List (BLit Φ)), m.Has L →
      (A.foldl (fun m h => if isFluent h && h.up != .note then
        (match litOf h.b with | some l => m.add l | none => m) else m) m).Has
        (L ++ (A.filter fun h => isFluent h && h.up != .note).filterMap fun h => litOf h.b) by
    simpa using this {} [] (Masks.has_nil _)
  induction A with
  | nil => intro m L h; simpa using h
  | cons a A ih =>
    intro m L h
    by_cases ha : (isFluent a && a.up != .note) = true
    · simp only [List.foldl_cons, List.filter_cons, ha, ↓reduceIte, List.filterMap_cons]
      cases hl : litOf a.b with
      | none => simpa using ih m L h
      | some l => simpa using ih (m.add l) (L ++ [l]) (Masks.has_add h l)
    · simp only [List.foldl_cons, List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte]
      exact ih m L h

theorem litsK_eq (hs : List (Held C Φ)) : litsK hs = lits hs := by
  have hA : K.filter (fun h : Held C Φ => h.up != .note && (litOf h.b).isSome) hs = adoptable hs := by
    rw [K.filter_eq]; rfl
  unfold litsK lits ordered
  dsimp only
  rw [hA]
  simp only [K.filterMap_eq, K.sortBy_eq, K.filter_eq, beforeK_eq]
  congr 2
  apply List.filter_congr
  intro h _
  have hk : (isFluent h && (match litOf h.b with | some l => (staleMasks (adoptable hs)).maybe l | none => false) &&
      staleK ((adoptable hs).filter fun h => isFluent h && h.up != .note) h) =
      (isFluent h && (match litOf h.b with | some l => (staleMasks (adoptable hs)).maybe l | none => false) &&
      stale (adoptable hs) h) := by
    cases hf : isFluent h
    · simp
    · rw [staleK_eq _ _ hf]
  rw [hk]
  -- a stale item is fluent and clashes with an adopted fluent item, which the masks have
  cases hs' : stale (adoptable hs) h
  · simp
  · have hst := hs'
    unfold stale at hst
    simp only [Bool.and_eq_true, List.any_eq_true] at hst
    obtain ⟨hf, h', hm', ⟨⟨hf', hn'⟩, _⟩, hc⟩ := hst
    cases hl : litOf h.b with
    | none => rw [hl] at hc; simp at hc
    | some l =>
      cases hl' : litOf h'.b with
      | none => rw [hl, hl'] at hc; simp at hc
      | some l' =>
        rw [hl, hl'] at hc
        dsimp only at hc
        cases hmb : (staleMasks (adoptable hs)).maybe l
        · have hin : l' ∈ ((adoptable hs).filter fun h => isFluent h && h.up != .note).filterMap
              fun h => litOf h.b :=
            List.mem_filterMap.mpr ⟨h', List.mem_filter.mpr ⟨hm', by simp [hf', hn']⟩, hl'⟩
          have := (Masks.no_clash (staleMasks_has _) l hmb l' hin).1
          rw [this] at hc; exact absurd hc (by decide)
        · simp [hf, hmb]

/-- What `c` now believes held at time `t`: their information about times up to `t`. -/
def viewAt (w : W) (c : C) (t : Nat) : List (BLit Φ) :=
  closure (admit (lits ((beliefs w c).filter (·.about ≤ t))))

/- Where a world keeps each character's record of the permanent conclusions they
have drawn (L5 in `abstractions/ROUND-1.md`): `HasMinds.settled`. Information
enters a base stamped with the time it arrives and the clock only moves on, so
the view a character had at a past time never changes: rather than rebuild every
past view to find what was settled then, a world can record the conclusions at
the end of each event (`recordSettled`, run by perception) and `view` reads the
record. Worlds without one (`none`, the default) rebuild the past views
(`settledAt`). The record lives in `HasMinds`, which `view` already takes, so a
world's record is the one `view` sees (a separate class would be resolved to its
default where `view` is defined). -/

/-- The permanent rule conclusions in the view of a base, the ones a record keeps. -/
def recordedHeads (hs : List (Held C Φ)) : List (BLit Φ) :=
  (closure (admit (lits hs))).filter fun l =>
    !Fluent.fluent l.1 && (Lore.rules (Φ := Φ)).any (·.head == l)

/-- A conclusion stays settled only if some lore rule gave it from premises that
are still believed (`now`) or merely went out of date (fluents); one drawn from a
premise the character has since given up goes with it. -/
def loreSurvives (now : List (BLit Φ)) (l : BLit Φ) : Bool := (Lore.rules (Φ := Φ)).any fun r =>
  r.head == l && r.body.all fun b => Fluent.fluent b.1 || now.contains b

/-- Permanent conclusions `c` drew at some time in their history that they no
longer hold as information, but that still stand. -/
def settledAt (w : W) (c : C) (base now : List (BLit Φ)) : List (BLit Φ) :=
  ((((beliefs w c).map (·.about)).eraseDups).flatMap fun t =>
    (viewAt w c t).filter fun l => !Fluent.fluent l.1 && !base.contains l && loreSurvives now l).eraseDups

/-- What `c` believes now (the definition; `view` computes it).  Changeable facts are judged by the most recent
information; permanent facts *concluded* (by the lore) about any earlier time
are kept, so "she held the letter then" still yields "she has read it". -/
def viewSpec (w : W) (c : C) : List (BLit Φ) :=
  let base := lits (beliefs w c)
  let now := closure (admit base)
  closure (admit (settledAt w c base now ++ base))

/-- Only a rule's head can be settled (`loreSurvives` asks for a rule that
concludes it): when no rule's head qualifies, nothing is settled, whatever the
history, and the per-time views need not be built. -/
theorem settledAt_guard (w : W) (c : C) (base now : List (BLit Φ)) :
    (if ((Lore.rules (Φ := Φ)).any fun r =>
        !Fluent.fluent r.head.1 && !base.contains r.head && loreSurvives now r.head) then
      settledAt w c base now else []) = settledAt w c base now := by
  split
  · rfl
  · rename_i h
    symm
    unfold settledAt
    have hq : ∀ l : BLit Φ, (!Fluent.fluent l.1 && !base.contains l && loreSurvives now l) = false := by
      intro l
      cases hl : (!Fluent.fluent l.1 && !base.contains l && loreSurvives now l)
      · rfl
      · exfalso
        apply h
        have hs : loreSurvives now l = true := by simp_all
        unfold loreSurvives at hs
        obtain ⟨r, hr, hrl⟩ := List.any_eq_true.mp hs
        have hh : r.head = l := by simp_all
        exact List.any_eq_true.mpr ⟨r, hr, by rw [hh]; exact hl⟩
    have hf : ∀ t, (viewAt w c t).filter (fun l => !Fluent.fluent l.1 && !base.contains l && loreSurvives now l) = [] :=
      fun t => List.filter_eq_nil_iff.mpr fun l _ => by rw [hq l]; exact Bool.false_ne_true
    simp only [hf]
    generalize (((beliefs w c).map (·.about)).eraseDups) = ts
    induction ts <;> simp_all

/-- What `c` believes now: `viewSpec`, computed without the work that cannot
change it. With no lore rules nothing is settled, so the per-time views are not
built; with nothing settled the view is `now`, which is not admitted twice
(`view_eq_viewSpec`). -/
def viewDef (w : W) (c : C) : List (BLit Φ) :=
  if (Lore.rules (Φ := Φ)).isEmpty then admitPlain (lits (beliefs w c)) else
  let base := lits (beliefs w c)
  let now := closure (admit base)
  -- the history is only consulted when some rule's head could be settled (`settledAt_guard`),
  -- and from the record when the world keeps one: the past views it records, then now
  let settled := if ((Lore.rules (Φ := Φ)).any fun r =>
      !Fluent.fluent r.head.1 && !base.contains r.head && loreSurvives now r.head) then
    (match HasMinds.settled w c with
     | some m =>
       -- an empty base has no past views, so nothing settled (`now` would add the
       -- heads of rules with empty bodies, and in another order)
       if (beliefs w c).isEmpty then [] else
       ((m ++ now).filter fun l =>
         !Fluent.fluent l.1 && !base.contains l && loreSurvives now l).eraseDups
     | none => settledAt w c base now) else []
  if settled.isEmpty then now else closure (admit (settled ++ base))

/-- `viewDef`, computed by the kernel's view (`litsK`, `admitK`): this is what every
check runs (`view_eq_viewDef`). -/
def view (w : W) (c : C) : List (BLit Φ) :=
  if (Lore.rules (Φ := Φ)).isEmpty then admitK (litsK (beliefs w c)) else
  let base := litsK (beliefs w c)
  let now := closureK (admitL base)
  -- the history is only consulted when some rule's head could be settled (`settledAt_guard`),
  -- and from the record when the world keeps one: the past views it records, then now
  let settled := if ((Lore.rules (Φ := Φ)).any fun r =>
      !Fluent.fluent r.head.1 && !base.contains r.head && loreSurvives now r.head) then
    (match HasMinds.settled w c with
     | some m =>
       -- an empty base has no past views, so nothing settled (`now` would add the
       -- heads of rules with empty bodies, and in another order)
       if (beliefs w c).isEmpty then [] else
       ((m ++ now).filter fun l =>
         !Fluent.fluent l.1 && !base.contains l && loreSurvives now l).eraseDups
     | none => settledAt w c base now) else []
  if settled.isEmpty then now else closureK (admitL (settled ++ base))

theorem view_eq_viewDef (w : W) (c : C) : view w c = viewDef w c := by
  unfold view viewDef
  simp only [litsK_eq, admitK_eq, admitL_eq, closureK_eq]

/-- Without a record, `view` computes `viewSpec`. With one, it does whenever the
record is right (`view_eq_viewSpec_of_rec`), which every event keeps
(`rec_next`); for the Studio, on every state a story reaches
(`Studio.view_run_start`). -/
theorem view_eq_viewSpec (w : W) (c : C) (hrec : HasMinds.settled w c = none) :
    view w c = viewSpec w c := by
  by_cases hr : Lore.rules (Φ := Φ) = []
  · have he : (Lore.rules (Φ := Φ)).isEmpty = true := List.isEmpty_iff.mpr hr
    have hz : ∀ ts : List Nat, (ts.flatMap fun t => (viewAt w c t).filter fun _ => false) = [] := by
      intro ts; induction ts <;> simp_all
    rw [view_eq_viewDef]; unfold viewDef viewSpec settledAt loreSurvives
    simp only [if_true, hr, List.any_nil, Bool.and_false, hz]
    simp only [List.isEmpty_nil, ite_true, List.eraseDups_nil, List.nil_append]
    rw [closure_of_nil hr, admit_eq_admitPlain hr]
  · have he : (Lore.rules (Φ := Φ)).isEmpty = false := by
      cases h : (Lore.rules (Φ := Φ)).isEmpty
      · rfl
      · exact absurd (List.isEmpty_iff.mp h) hr
    rw [view_eq_viewDef]; unfold viewDef viewSpec
    simp only [he, Bool.false_eq_true, ite_false, hrec, settledAt_guard]
    split
    · rename_i h
      rw [List.isEmpty_iff.mp h]; rfl
    · rfl

/-- What `c` believed at story time `s`, as they remember it: the view their
base had then. -/
def viewAsOf (w : W) (c : C) (s : Nat) : List (BLit Φ) :=
  closure (admit (lits ((beliefs w c).filter (·.heard ≤ s))))

/-- What `c` thinks `d` believes. -/
def viewOf (w : W) (c d : C) : List (BLit Φ) :=
  closure (admit ((ordered (beliefs w c)).filterMap fun h => match h.b with
    | .bel d' b => if d' == d then litOf b else none
    | _ => none))

theorem view_consistent (w : W) (c : C)
    (h : consistent (closure ([] : List (BLit Φ))) = true) :
    consistent (view w c) = true := by
  rw [view_eq_viewDef]
  unfold viewDef
  split
  · rename_i he
    have hr := List.isEmpty_iff.mp he
    rw [← admit_eq_admitPlain hr, ← closure_of_nil hr (admit _)]
    exact admit_consistent _ h
  · dsimp only
    repeat' split
    all_goals exact admit_consistent _ h

/-- `c` now believes `φ` held at time `t`. -/
def thinksWas (w : W) (c : C) (φ : Φ) (t : Nat) : Bool := (viewAt w c t).contains (φ, true)
/-- At time `s`, `c` believed `l` (and can remember that they did). -/
def believedAt (w : W) (c : C) (s : Nat) (l : BLit Φ) : Bool := (viewAsOf w c s).contains l

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

/-- The prior for the evidence, then each named adjustment. -/
def reasonsFor (w : W) (c : C) (e : Evid C) (l : BLit Φ) : List (Reason × Int) :=
  (.prior e.kind, e.prior) :: Credence.reasons w c e l

def strength (w : W) (c : C) (e : Evid C) (l : BLit Φ) : Int :=
  ((reasonsFor w c e l).map (·.2)).sum

/-- The hearer's attitude to information of strength `s`. -/
def attitude (w : W) (c : C) (e : Evid C) (l : BLit Φ) : Upgrade :=
  let s := strength w c e l
  if e == .self then .hard
  else if s ≥ Credence.acceptAt (Φ := Φ) w c then
    (if Credence.stubborn (Φ := Φ) w c then .conservative else .radical)
  else if s ≥ Credence.acceptAt (Φ := Φ) w c - 1 then .conservative
  else .note

private def stampOf (hs : List (Held C Φ)) : Nat := hs.foldl (fun m h => max m h.stamp) 0 + 1

private def insert (w : W) (hs : List (Held C Φ)) (b : Belief C Φ) (e : Evid C) (u : Upgrade)
    (rank : Nat) (rs : List (Reason × Int)) : List (Held C Φ) :=
  hs ++ [{ b, src := e, rank, stamp := stampOf hs, up := u,
           heard := Clock.now w, about := Clock.now w, reasons := rs }]

private def content : Belief C Φ → Option (BLit Φ)
  | .bel _ b => content b
  | b => litOf b

/-- `c` comes to have `b` by evidence `e`. Testimony also records that the
speaker said it. A perception that clashes with an uncaught report from `d`
catches `d` out (unless `check` is off: see `witness`). -/
def learnWith (check : Bool) (w : W) (c : C) (b : Belief C Φ) (e : Evid C) : W :=
  match content b with
  | none => w
  | some l =>
  let u := attitude w c e l
  let rs := reasonsFor w c e l
  let rank := if u == .hard then 10 else (strength w c e l).toNat
  let hs := insert w (beliefs w c) b e u rank rs
  let hs := match e.speaker with
    | some d => insert w hs (.bel d b) e .radical rank rs
    | none => hs
  let w := setBeliefs w c hs
  if !check || !e.perceptual then w else
  let v := view w c
  -- a report clashes with the view only if its bits are set in the view's masks (`liar_test`)
  let mv := masksOf v
  let liars := (beliefs w c).filterMap fun h =>
    match h.src.speaker, litOf h.b with
    | some d, some l => if !h.caught && h.up != .note && (mv.maybe l && K.any v (clash l)) then some (h, d) else none
    | _, _ => none
  let w := setBeliefs w c ((beliefs w c).map fun h =>
    -- stamps are unique within a base, so comparing them finds the same items
    -- as comparing whole items, without comparing everything they carry
    if liars.any (·.1.stamp == h.stamp) then { h with caught := true } else h)
  liars.foldl (fun w (_, d) => Credence.onBetrayal (Φ := Φ) w c d) w

def learn (w : W) (c : C) (b : Belief C Φ) (e : Evid C) : W := learnWith true w c b e

/-- The liar check `learnWith` runs: a literal clashes with the view only if its bits
are set in the view's masks, so the scan can wait for them. -/
theorem liar_test (v : List (BLit Φ)) (l : BLit Φ) :
    ((masksOf v).maybe l && K.any v (clash l)) = v.any (clash l) := by
  rw [K.any_eq]
  cases hm : (masksOf v).maybe l
  · simp only [Bool.false_and]
    symm
    rw [List.any_eq_false]
    intro y hy
    simp [(Masks.no_clash (masksOf_ok v).1 l hm y hy).1]
  · simp

/-- Everyone at `p` who perceives sees `φs`, and sees the other perceivers see
them.

Each witness learns `φ`, which runs the check for reports `φ` catches out, and
then that each other witness saw it. Those nested beliefs are learned without
the check: a nested belief does not enter the view (`lits` keeps first-order
literals only) and has no speaker, so right after the check for `φ` the same
check could find no one new. Skipping it gives the same state, one view per
fact instead of one per pair of witnesses. -/
def witness [Cast C] [Perceives W C] (w : W) (p : P) (φs : List Φ) : W :=
  let present := Cast.all.filter fun x => loc w x == p && Perceives.perceives w x
  present.foldl (fun w x =>
    φs.foldl (fun w φ =>
      ((present.filter (· != x)).foldl (fun w y => learnWith false w x (.bel y (.atom φ)) .seen)
        (learn w x (.atom φ) .seen))) w) w

/-- Speech needs a speaker and a listener who can perceive (the dead neither
talk nor hear); noticing and realising need a mind that can. -/
def mindOk3 [Perceives W C] (w : W) : MindEv C Φ → Tri
  | .tell c d l | .whisper c d l =>
    if !Perceives.perceives w c || !Perceives.perceives w d then .no else
    (together3 w c d).and (Tri.ofBool ((view w c).contains l))
  | .lie c d l =>
    if !Perceives.perceives w c || !Perceives.perceives w d then .no else
    (together3 w c d).and (Tri.ofBool (!(view w c).contains l))
  | .message c d l =>
    if !Perceives.perceives w c || !Perceives.perceives w d then .no else
    Tri.ofBool ((view w c).contains l)
  | .notice c l e => Tri.ofBool (Perceives.perceives w c && (!e.perceptual || truthLit w l))
  | .realise c l => Tri.ofBool (Perceives.perceives w c && truthLit w l && (closureK (view w c)).contains l)

/-- Who in a mind event cannot perceive, said as a reason. -/
def mindDead [Perceives W C] (w : W) : MindEv C Φ → Option String
  | .tell c d _ | .whisper c d _ | .lie c d _ | .message c d _ =>
    if !Perceives.perceives w c then some "the speaker cannot speak (dead, or no mind)"
    else if !Perceives.perceives w d then some "the listener cannot hear (dead, or no mind)"
    else none
  | .notice c _ _ | .realise c _ =>
    if !Perceives.perceives w c then some "they cannot perceive (dead, or no mind)" else none

instance [Cast C] [Perceives W C] : Domain W (MindEv C Φ) where
  ok3 := mindOk3
  ok w e := mindOk3 w e == .yes
  step w
    | .tell c d l =>
      let w := meet w c d
      let hearers := Cast.all.filter fun x => x != c && loc w x == loc w c && Perceives.perceives w x
      let w := hearers.foldl (fun w x => learn w x (ofLit l) (.told c)) w
      learn w c (.bel d (ofLit l)) .self
    | .whisper c d l | .lie c d l =>
      let w := meet w c d
      learn (learn w d (ofLit l) (.told c)) c (.bel d (ofLit l)) .self
    | .message c d l => learn (learn w d (ofLit l) (.told c)) c (.bel d (ofLit l)) .self
    | .notice c l e => learn w c (ofLit l) e
    | .realise c l => learn w c (ofLit l) .inferred
  why w e := (mindDead w e).getD (match e with
    | .tell c d _ | .whisper c d _ =>
      if together3 w c d == .unknown then "assumes they were together"
      else if loc w c != loc w d then "they are not together" else "the speaker does not think that"
    | .lie c d _ => if together3 w c d == .unknown then "assumes they were together"
                    else if loc w c != loc w d then "they are not together"
                    else "the speaker thinks it is true, so it is not a lie"
    | .message _ _ _ => "the sender does not think that"
    | .notice _ _ _ => "a perception must be of something true"
    | .realise _ l => if !truthLit w l then "the text says they know it, but it is false"
                      else "they have no way to know that")

/-! ## Explanations -/

section
variable [Repr Φ] [Repr C]

private def litStr (l : BLit Φ) : String := (if l.2 then "" else "not ") ++ reprStr l.1

/-- Why `c` holds what they hold about `l`: for each piece of evidence, its
reasons and strength, the attitude it got, and whether it is believed now. -/
def explain (w : W) (c : C) (l : BLit Φ) : List String :=
  let v := view w c
  (beliefs w c).filterMap fun h => do
    let l' ← litOf h.b
    if l'.1 != l.1 then none else
    let rs := ", ".intercalate (h.reasons.map fun (r, n) => s!"{r.text Φ} {if n ≥ 0 then "+" else ""}{n}")
    let s := (h.reasons.map (·.2)).sum
    let status :=
      if h.up == .note then "only noted"
      else if v.contains l' then "believed now"
      else match v.find? (clash l') with
        | some x => s!"outranked by {litStr x}"
        | none => "not believed"
    return s!"{litStr l'} ({rs} = {s}; {reprStr h.up}): {status}"
end

/-- `recordedHeads`, computed by the kernel's view (`recordedHeadsK_eq`). -/
def recordedHeadsK (hs : List (Held C Φ)) : List (BLit Φ) :=
  (closureK (admitL (litsK hs))).filter fun l =>
    !Fluent.fluent l.1 && (Lore.rules (Φ := Φ)).any (·.head == l)

theorem recordedHeadsK_eq (hs : List (Held C Φ)) : recordedHeadsK hs = recordedHeads hs := by
  unfold recordedHeadsK recordedHeads
  rw [litsK_eq, admitL_eq, closureK_eq]

/-- One character's turn in `recordSettled`: the new permanent conclusions in their
view, if they have a record and (after the first event) their base changed in this
event (`before` is the state the event started from). -/
def recordOne (before w : W) (c : C) : W :=
  match HasMinds.settled w c with
  | none => w
  | some m =>
    -- by content, not length: a revision can replace a belief and keep the count;
    -- the kernel decides an unchanged base equal at once (cheaper than looking
    -- through the base for information about the present)
    if (beliefs w c).isEmpty || (decide (beliefs before c = beliefs w c) && Clock.now w != 0) then w else
    match (recordedHeadsK (beliefs w c)).filter (!m.contains ·) with
    | [] => w
    | hs => HasMinds.setSettled w c (m ++ hs)

/-- At the end of an event, each character whose base changed records the permanent
conclusions in their view (`HasMinds.settled`); nothing to do without lore or without
a record. The clock then moves on, so this view is the one they will always have had
of this time (`view_eq_viewSpec_of_rec`). At the end of the first event (time 0)
everyone with a base records, so the opening knowledge, stamped 0 too, is recorded
after anything that event revised. -/
def recordSettled [Cast C] (before w : W) : W :=
  if (Lore.rules (Φ := Φ)).isEmpty then w else (Cast.all : List C).foldl (recordOne before) w

/-- Witnessing: after each event, those present see what it showed, and then
record what they have settled. -/
instance {E : Type} [Cast C] [Perceives W C] [Observable W E Φ P] : Perceive W E where
  perceive before e after :=
    recordSettled before (match Observable.seen before e with
      | some (p, φs) => witness after p φs
      | none => after)

/-! ## L5 is exact: with a well-kept record, `view` is `viewSpec`

`viewSpec` rebuilds the view of every past time to find the conclusions settled
then; `view` reads them from the record. They agree whenever the record holds,
up to repeats, the recorded heads of the view of each past time, oldest first
(`pastHeads`), which is what `settledAt` visits. `RecOk w c` says so, for a base
that is the past followed by the present; `view_eq_viewSpec_of_rec` turns it
into the equation, `rec_next` and `rec_run` carry it along a story, and
`grows_rec` through the middle of an event (where `learnWith` builds views
too). What it needs of a world is `LawfulMinds`: the bases and the record are
separate fields, catching a liar out touches neither, and the clock moves on
after each event; and of its events, that they only learn (`Grows`). -/

section Record

/-- An item as a view reads it: whether its source was caught out does not matter. -/
def Held.plain (h : Held C Φ) : Held C Φ := { h with caught := false }

/-- The recorded heads of the view at each time a base has information about,
oldest first: the lists `settledAt` collects, before it filters them. -/
def pastHeads (hs : List (Held C Φ)) : List (BLit Φ) :=
  ((hs.map (·.about)).eraseDups).flatMap fun t => recordedHeads (hs.filter (·.about ≤ t))

/-! ### Lists -/

theorem insertBy_map {α β : Type} (le : α → α → Bool) (le' : β → β → Bool) (f : α → β)
    (hf : ∀ x y, le' (f x) (f y) = le x y) (x : α) :
    ∀ xs : List α, insertBy le' (f x) (xs.map f) = (insertBy le x xs).map f
  | [] => rfl
  | y :: ys => by
    simp only [List.map_cons, insertBy, hf]
    cases le x y <;> simp [insertBy_map le le' f hf x ys]

theorem sortBy_map {α β : Type} (le : α → α → Bool) (le' : β → β → Bool) (f : α → β)
    (hf : ∀ x y, le' (f x) (f y) = le x y) :
    ∀ xs : List α, sortBy le' (xs.map f) = (sortBy le xs).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, sortBy, sortBy_map le le' f hf xs, insertBy_map le le' f hf]

theorem eraseDups_append_congr {α : Type} [BEq α] [LawfulBEq α] {A A' : List α} (X : List α)
    (h : A.eraseDups = A'.eraseDups) : (A ++ X).eraseDups = (A' ++ X).eraseDups := by
  have hm : ∀ x, A.elem x = A'.elem x := by
    intro x
    have : x ∈ A ↔ x ∈ A' := by rw [← List.mem_eraseDups, h, List.mem_eraseDups]
    simp [this]
  rw [List.eraseDups_append, List.eraseDups_append, h]
  unfold List.removeAll
  simp only [hm]

theorem eraseDups_append_of_sub {α : Type} [BEq α] [LawfulBEq α] (A X : List α)
    (h : ∀ x ∈ X, x ∈ A) : (A ++ X).eraseDups = A.eraseDups := by
  rw [List.eraseDups_append]
  have : X.removeAll A = [] := by
    unfold List.removeAll
    exact List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx]
  rw [this]; simp

theorem eraseDups_append_new {α : Type} [BEq α] [LawfulBEq α] (m X : List α) :
    (m ++ X.filter (!m.contains ·)).eraseDups = (m ++ X).eraseDups := by
  rw [List.eraseDups_append, List.eraseDups_append]
  unfold List.removeAll
  rw [List.filter_filter]
  simp

theorem eraseDups_filter {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {L : List α} :
    (L.filter p).eraseDups = L.eraseDups.filter p := by
  match L with
  | [] => rfl
  | a :: as =>
    have : (as.filter fun b => !b == a).length < as.length + 1 :=
      Nat.lt_add_one_of_le (List.length_filter_le _ as)
    have ih := eraseDups_filter p (L := as.filter fun b => !b == a)
    rw [List.eraseDups_cons]
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp, List.eraseDups_cons, List.filter_cons_of_pos hp, ← ih,
        List.filter_filter, List.filter_filter]
      congr 3
      funext b
      exact Bool.and_comm _ _
    · rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg hp, ← ih, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro b _
      by_cases hb : b = a
      · subst hb; simp [hp]
      · simp [hb]
termination_by L.length

theorem exists_max_nat (l : List Nat) (hl : l ≠ []) : ∃ t ∈ l, ∀ x ∈ l, x ≤ t := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    by_cases hn : l = []
    · subst hn; exact ⟨a, by simp, by simp⟩
    · obtain ⟨t, ht, hm⟩ := ih hn
      by_cases hat : a ≤ t
      · refine ⟨t, List.mem_cons_of_mem _ ht, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hat
        · exact hm x hx
      · refine ⟨a, by simp, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_trans (hm x hx) (by omega)

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons, h x (by simp), flatMap_congr_mem (l := l) (fun y hy => h y (by simp [hy]))]

/-! ### What views read of a base -/

theorem lits_map_plain (hs : List (Held C Φ)) : lits (hs.map Held.plain) = lits hs := by
  have ha : adoptable (hs.map Held.plain) = (adoptable hs).map Held.plain := by
    unfold adoptable; rw [List.filter_map]; rfl
  have hst : ∀ (A : List (Held C Φ)) h, stale (A.map Held.plain) (Held.plain h) = stale A h := by
    intro A h; unfold stale; rw [List.any_map]; rfl
  unfold lits
  simp only []
  rw [ha, List.filter_map]
  have hp : ((fun h => !stale ((adoptable hs).map Held.plain) h) ∘ Held.plain) =
      fun h => !stale (adoptable hs) h := by
    funext h; simp only [Function.comp, hst]
  rw [hp]
  unfold ordered
  rw [sortBy_map before before Held.plain (fun _ _ => rfl), List.filterMap_map]
  rfl

theorem recordedHeads_map_plain (hs : List (Held C Φ)) :
    recordedHeads (hs.map Held.plain) = recordedHeads hs := by
  unfold recordedHeads; rw [lits_map_plain]

theorem pastHeads_map_plain (hs : List (Held C Φ)) : pastHeads (hs.map Held.plain) = pastHeads hs := by
  unfold pastHeads
  rw [List.map_map]
  apply flatMap_congr_mem
  intro t _
  rw [List.filter_map]
  exact recordedHeads_map_plain _

/-- A base's present view is among the views of its times. -/
theorem recordedHeads_sub_pastHeads (hs : List (Held C Φ)) (hne : hs ≠ []) :
    ∀ x ∈ recordedHeads hs, x ∈ pastHeads hs := by
  intro x hx
  obtain ⟨t, ht, hmax⟩ := exists_max_nat (hs.map (·.about)) (by simpa using hne)
  have hf : hs.filter (·.about ≤ t) = hs :=
    List.filter_eq_self.mpr fun h hh => by simpa using hmax _ (List.mem_map_of_mem hh)
  unfold pastHeads
  exact List.mem_flatMap.mpr ⟨t, List.mem_eraseDups.mpr ht, by rw [hf]; exact hx⟩

/-- The views of a base that is the past (`B₁`) then the present (`B₂`): the past's
views, then the present one. -/
theorem pastHeads_present (B₁ B₂ : List (Held C Φ)) (N : Nat) (h₁ : ∀ h ∈ B₁, h.about < N)
    (h₂ : ∀ h ∈ B₂, h.about = N) (hne : B₁ ++ B₂ ≠ []) :
    (pastHeads B₁ ++ recordedHeads (B₁ ++ B₂)).eraseDups = (pastHeads (B₁ ++ B₂)).eraseDups := by
  let R := recordedHeads (B₁ ++ B₂)
  let rest := ((B₂.map (·.about)).removeAll (B₁.map (·.about))).eraseDups
  have hrest : ∀ t ∈ rest, t = N := by
    intro t ht
    have := List.mem_eraseDups.mp ht
    unfold List.removeAll at this
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp (List.mem_filter.mp this).1
    exact h₂ h hh
  have hdecomp : pastHeads (B₁ ++ B₂) = pastHeads B₁ ++ rest.flatMap fun _ => R := by
    unfold pastHeads
    rw [List.map_append, List.eraseDups_append, List.flatMap_append]
    congr 1
    · apply flatMap_congr_mem
      intro t ht
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp ht)
      have hlt := h₁ h hh
      have e2 : B₂.filter (·.about ≤ h.about) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx => by simp [h₂ x hx]; omega
      rw [List.filter_append, e2, List.append_nil]
    · apply flatMap_congr_mem
      intro t ht
      rw [hrest t ht, List.filter_eq_self.mpr]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · simpa using Nat.le_of_lt (h₁ x hx)
      · simp [h₂ x hx]
  rw [hdecomp]
  cases hr : rest with
  | nil =>
    have hsub := recordedHeads_sub_pastHeads (B₁ ++ B₂) hne
    rw [hdecomp, hr] at hsub
    simp only [List.flatMap_nil, List.append_nil] at hsub ⊢
    exact eraseDups_append_of_sub _ _ hsub
  | cons t ts =>
    simp only [List.flatMap_cons]
    rw [← List.append_assoc, eraseDups_append_of_sub (pastHeads B₁ ++ R)]
    intro x hx
    obtain ⟨_, _, hx⟩ := List.mem_flatMap.mp hx
    exact List.mem_append_right _ hx

/-- `settledAt` is `pastHeads`, filtered: a conclusion that still stands is a rule head. -/
theorem settledAt_eq_pastHeads (w : W) (c : C) (base now : List (BLit Φ)) :
    settledAt w c base now = ((pastHeads (beliefs w c)).filter fun l =>
      !Fluent.fluent l.1 && !base.contains l && loreSurvives now l).eraseDups := by
  unfold settledAt pastHeads
  rw [List.filter_flatMap]
  congr 1
  apply flatMap_congr_mem
  intro t _
  unfold viewAt recordedHeads
  rw [List.filter_filter]
  apply List.filter_congr
  intro l _
  cases hq : (!Fluent.fluent l.1 && !base.contains l && loreSurvives now l)
  · rfl
  · simp only [Bool.true_and]
    simp only [Bool.and_eq_true] at hq
    obtain ⟨⟨hf, -⟩, hs⟩ := hq
    unfold loreSurvives at hs
    obtain ⟨r, hr, hrl⟩ := List.any_eq_true.mp hs
    simp only [Bool.and_eq_true] at hrl
    rw [hf, Bool.true_and]
    exact (List.any_eq_true.mpr ⟨r, hr, hrl.1⟩).symm

/-! ### The invariant -/

/-- The record of `c` is right: `c`'s base, as views read it, is the past (`B₁`, about
earlier times) then the present (`B₂`, about now), and a record holds the views of
the past (`pastHeads B₁`), up to repeats. Only the cast keeps a record. -/
def RecOk [Cast C] (w : W) (c : C) : Prop :=
  ∃ B₁ B₂ : List (Held C Φ), (beliefs w c).map Held.plain = B₁ ++ B₂ ∧
    (∀ h ∈ B₁, h.about < Clock.now w) ∧ (∀ h ∈ B₂, h.about = Clock.now w) ∧
    ∀ m, HasMinds.settled w c = some m → c ∈ (Cast.all : List C) ∧
      m.eraseDups = (pastHeads B₁).eraseDups

/-- Every character's record is right. -/
def Rec [Cast C] (w : W) : Prop := ∀ c : C, RecOk (Φ := Φ) w c

/-- The fast path is the definition: with a right record, `view` (which reads it)
is `viewSpec` (which rebuilds every past view). -/
theorem view_eq_viewSpec_of_rec [Cast C] (w : W) (c : C) (h : RecOk (Φ := Φ) w c) :
    view w c = viewSpec w c := by
  cases hm : HasMinds.settled w c with
  | none => exact view_eq_viewSpec w c hm
  | some m =>
  obtain ⟨B₁, B₂, hB, h₁, h₂, hr⟩ := h
  have hrm := (hr m hm).2
  by_cases hr0 : Lore.rules (Φ := Φ) = []
  · have he : (Lore.rules (Φ := Φ)).isEmpty = true := List.isEmpty_iff.mpr hr0
    have hz : ∀ ts : List Nat, (ts.flatMap fun t => (viewAt w c t).filter fun _ => false) = [] := by
      intro ts; induction ts <;> simp_all
    rw [view_eq_viewDef]; unfold viewDef viewSpec settledAt loreSurvives
    simp only [hr0, List.any_nil, Bool.and_false, hz]
    simp only [List.isEmpty_nil, ite_true, List.eraseDups_nil, List.nil_append]
    rw [closure_of_nil hr0, admit_eq_admitPlain hr0]
  · have he : (Lore.rules (Φ := Φ)).isEmpty = false := by
      cases h : (Lore.rules (Φ := Φ)).isEmpty
      · rfl
      · exact absurd (List.isEmpty_iff.mp h) hr0
    -- the settled list `view` computes is `settledAt`
    have key : ∀ (base now : List (BLit Φ)), base = lits (beliefs w c) → now = closure (admit base) →
        (if ((Lore.rules (Φ := Φ)).any fun r =>
            !Fluent.fluent r.head.1 && !base.contains r.head && loreSurvives now r.head) then
          (if (beliefs w c).isEmpty then [] else
            ((m ++ now).filter fun l => !Fluent.fluent l.1 && !base.contains l && loreSurvives now l).eraseDups)
         else []) = settledAt w c base now := by
      intro base now hbase hnow
      rw [← settledAt_guard w c base now]
      split
      · split
        · rename_i hemp
          unfold settledAt
          rw [List.isEmpty_iff.mp hemp]
          rfl
        · rename_i hemp
          have hne : B₁ ++ B₂ ≠ [] := by
            rw [← hB]; simpa [List.isEmpty_iff] using hemp
          rw [settledAt_eq_pastHeads, ← pastHeads_map_plain, hB]
          -- `now`'s rule heads are the base's recorded heads
          have hnowf : ∀ q : BLit Φ → Bool, (∀ l, q l = true → !Fluent.fluent l.1 &&
              (Lore.rules (Φ := Φ)).any (·.head == l)) → now.filter q =
                (recordedHeads (B₁ ++ B₂)).filter q := by
            intro q hq
            rw [← hB, recordedHeads_map_plain]
            unfold recordedHeads
            rw [hnow, hbase, List.filter_filter]
            apply List.filter_congr
            intro l _
            cases hql : q l
            · rfl
            · simp [hq l hql]
          rw [List.filter_append, hnowf, ← List.filter_append, eraseDups_filter, eraseDups_filter,
            eraseDups_append_congr _ hrm, pastHeads_present B₁ B₂ _ h₁ h₂ hne]
          intro l hl
          simp only [Bool.and_eq_true] at hl
          obtain ⟨⟨hf, -⟩, hs⟩ := hl
          unfold loreSurvives at hs
          obtain ⟨r, hr, hrl⟩ := List.any_eq_true.mp hs
          simp only [Bool.and_eq_true] at hrl
          simp only [hf, Bool.true_and]
          exact List.any_eq_true.mpr ⟨r, hr, hrl.1⟩
      · rfl
    rw [view_eq_viewDef]; unfold viewDef viewSpec
    simp only [he, Bool.false_eq_true, ite_false, hm]
    rw [key _ _ rfl rfl]
    split
    · rename_i hemp
      rw [List.isEmpty_iff.mp hemp]; rfl
    · rfl

/-! ### Keeping it: the laws, and what events may do -/

/-- What L5 needs of a world: the bases and the record are separate fields (a
record is set only where one is kept), catching a liar out touches neither, and
the clock moves on after each event (so the past stays past). -/
class LawfulMinds (W : Type) (C Φ : outParam Type) [DecidableEq C] [HasMinds W C Φ] [Clock W]
    [Credence W C Φ] : Prop where
  beliefs_setBeliefs (w : W) (c c' : C) (bs : List (Held C Φ)) :
    HasMinds.beliefs (HasMinds.setBeliefs w c bs) c' = if c' = c then bs else HasMinds.beliefs w c'
  settled_setBeliefs (w : W) (c c' : C) (bs : List (Held C Φ)) :
    HasMinds.settled (HasMinds.setBeliefs w c bs) c' = HasMinds.settled w c'
  now_setBeliefs (w : W) (c : C) (bs : List (Held C Φ)) :
    Clock.now (HasMinds.setBeliefs w c bs) = Clock.now w
  beliefs_setSettled (w : W) (c c' : C) (m : List (Φ × Bool)) :
    HasMinds.beliefs (HasMinds.setSettled w c m) c' = HasMinds.beliefs w c'
  settled_setSettled (w : W) (c c' : C) (m m₀ : List (Φ × Bool)) : HasMinds.settled w c = some m₀ →
    HasMinds.settled (HasMinds.setSettled w c m) c' = if c' = c then some m else HasMinds.settled w c'
  now_setSettled (w : W) (c : C) (m : List (Φ × Bool)) :
    Clock.now (HasMinds.setSettled w c m) = Clock.now w
  beliefs_onBetrayal (w : W) (c d c' : C) :
    HasMinds.beliefs (Credence.onBetrayal (Φ := Φ) w c d) c' = HasMinds.beliefs w c'
  settled_onBetrayal (w : W) (c d c' : C) :
    HasMinds.settled (Credence.onBetrayal (Φ := Φ) w c d) c' = HasMinds.settled w c'
  now_onBetrayal (w : W) (c d : C) : Clock.now (Credence.onBetrayal (Φ := Φ) w c d) = Clock.now w
  beliefs_tick (w : W) (c : C) : HasMinds.beliefs (Clock.tick w) c = HasMinds.beliefs w c
  settled_tick (w : W) (c : C) : HasMinds.settled (Clock.tick w) c = HasMinds.settled w c
  now_lt_tick (w : W) : Clock.now w < Clock.now (Clock.tick w)

/-- `w'` is `w` with information about the present added to bases (and sources
perhaps caught out), the record and the clock untouched: what learning does in the
middle of an event. -/
def Grows (w w' : W) : Prop :=
  Clock.now w' = Clock.now w ∧ ∀ c : C, HasMinds.settled w' c = HasMinds.settled w c ∧
    ∃ X : List (Held C Φ), (beliefs w' c).map Held.plain = (beliefs w c).map Held.plain ++ X ∧
      ∀ h ∈ X, h.about = Clock.now w

theorem Grows.refl (w : W) : Grows (C := C) (Φ := Φ) w w :=
  ⟨rfl, fun _ => ⟨rfl, [], by simp, by simp⟩⟩

theorem Grows.trans {w₁ w₂ w₃ : W} (h₁ : Grows (C := C) (Φ := Φ) w₁ w₂)
    (h₂ : Grows (C := C) (Φ := Φ) w₂ w₃) : Grows (C := C) (Φ := Φ) w₁ w₃ := by
  obtain ⟨hn₁, hc₁⟩ := h₁
  obtain ⟨hn₂, hc₂⟩ := h₂
  refine ⟨hn₂.trans hn₁, fun c => ?_⟩
  obtain ⟨hs₁, X₁, hX₁, ha₁⟩ := hc₁ c
  obtain ⟨hs₂, X₂, hX₂, ha₂⟩ := hc₂ c
  refine ⟨hs₂.trans hs₁, X₁ ++ X₂, by rw [hX₂, hX₁, List.append_assoc], fun h hh => ?_⟩
  rcases List.mem_append.mp hh with hh | hh
  · exact ha₁ h hh
  · rw [ha₂ h hh, hn₁]

theorem grows_of_frame {w w' : W} (hn : Clock.now w' = Clock.now w)
    (hs : ∀ c : C, HasMinds.settled w' c = HasMinds.settled w c)
    (hb : ∀ c, beliefs w' c = beliefs w c) : Grows (C := C) (Φ := Φ) w w' :=
  ⟨hn, fun c => ⟨hs c, [], by rw [hb c, List.append_nil], by simp⟩⟩

theorem grows_foldl {β : Type} (f : W → β → W) (hf : ∀ w x, Grows (C := C) (Φ := Φ) w (f w x)) :
    ∀ (l : List β) (w : W), Grows (C := C) (Φ := Φ) w (l.foldl f w)
  | [], w => Grows.refl w
  | x :: l, w => Grows.trans (hf w x) (grows_foldl f hf l (f w x))

/-- `hs'` is `hs` with items about the present added at the end (as views read them). -/
def Appended (now : Nat) (hs hs' : List (Held C Φ)) : Prop :=
  ∃ X : List (Held C Φ), hs'.map Held.plain = hs.map Held.plain ++ X ∧ ∀ h ∈ X, h.about = now

theorem appended_insert (w : W) (hs : List (Held C Φ)) (b : Belief C Φ) (e : Evid C) (u : Upgrade)
    (rank : Nat) (rs : List (Reason × Int)) : Appended (Clock.now w) hs (insert w hs b e u rank rs) := by
  let x : Held C Φ :=
    { b, src := e, rank, stamp := stampOf hs, up := u, heard := Clock.now w, about := Clock.now w, reasons := rs }
  refine ⟨[Held.plain x], ?_, ?_⟩
  · simp [insert]; rfl
  · simp only [List.mem_singleton]; rintro _ rfl; rfl

theorem Appended.trans {n : Nat} {hs₁ hs₂ hs₃ : List (Held C Φ)} (h₁ : Appended n hs₁ hs₂)
    (h₂ : Appended n hs₂ hs₃) : Appended n hs₁ hs₃ := by
  obtain ⟨X₁, hX₁, ha₁⟩ := h₁
  obtain ⟨X₂, hX₂, ha₂⟩ := h₂
  refine ⟨X₁ ++ X₂, by rw [hX₂, hX₁, List.append_assoc], fun h hh => ?_⟩
  rcases List.mem_append.mp hh with hh | hh
  · exact ha₁ h hh
  · exact ha₂ h hh

theorem grows_setBeliefs [LawfulMinds W C Φ] (w : W) (c : C) (bs : List (Held C Φ))
    (h : Appended (Clock.now w) (beliefs w c) bs) : Grows (C := C) (Φ := Φ) w (setBeliefs w c bs) := by
  obtain ⟨X, hX, ha⟩ := h
  refine ⟨LawfulMinds.now_setBeliefs w c bs, fun c' => ⟨LawfulMinds.settled_setBeliefs w c c' bs, ?_⟩⟩
  rw [LawfulMinds.beliefs_setBeliefs]
  split
  · rename_i hc; subst hc; exact ⟨X, hX, ha⟩
  · exact ⟨[], by simp, by simp⟩

theorem plain_mark (b : Bool) (h : Held C Φ) :
    Held.plain (if b = true then { h with caught := true } else h) = Held.plain h := by
  cases b <;> rfl

/-- Catching sources out changes nothing a view reads. -/
theorem grows_mark [LawfulMinds W C Φ] (w : W) (c : C) (f : Held C Φ → Held C Φ)
    (hf : ∀ h, Held.plain (f h) = Held.plain h) :
    Grows (C := C) (Φ := Φ) w (setBeliefs w c ((beliefs w c).map f)) :=
  grows_setBeliefs w c _ ⟨[], by rw [List.map_map, List.append_nil]; exact List.map_congr_left (fun h _ => hf h), by simp⟩

theorem learnWith_grows [LawfulMinds W C Φ] (k : Bool) (w : W) (c : C) (b : Belief C Φ) (e : Evid C) :
    Grows (C := C) (Φ := Φ) w (learnWith k w c b e) := by
  unfold learnWith
  split
  · exact Grows.refl w
  · simp only []
    -- the items added, then (when checking) sources caught out, then betrayals
    have hbetray : ∀ (l : List (Held C Φ × C)) (w' : W), Grows (C := C) (Φ := Φ) w'
        (l.foldl (fun w (_, d) => Credence.onBetrayal (Φ := Φ) w c d) w') :=
      grows_foldl _ fun w x => by
        rcases x with ⟨_, d⟩
        exact grows_of_frame (LawfulMinds.now_onBetrayal w c d)
          (LawfulMinds.settled_onBetrayal w c d) (LawfulMinds.beliefs_onBetrayal w c d)
    by_cases hk : (!k || !e.perceptual) = true
    · simp only [hk, ↓reduceIte]
      cases e.speaker with
      | none => exact grows_setBeliefs w c _ (appended_insert ..)
      | some d => exact grows_setBeliefs w c _ (Appended.trans (appended_insert ..) (appended_insert ..))
    · simp only [hk, ↓reduceIte, Bool.false_eq_true]
      refine Grows.trans ?_ (hbetray _ _)
      cases e.speaker with
      | none =>
        exact Grows.trans (grows_setBeliefs w c _ (appended_insert ..)) (grows_mark _ c _ fun h => plain_mark _ h)
      | some d =>
        exact Grows.trans (grows_setBeliefs w c _ (Appended.trans (appended_insert ..) (appended_insert ..)))
          (grows_mark _ c _ fun h => plain_mark _ h)

theorem learn_grows [LawfulMinds W C Φ] (w : W) (c : C) (b : Belief C Φ) (e : Evid C) :
    Grows (C := C) (Φ := Φ) w (learn w c b e) := learnWith_grows true w c b e

theorem witness_grows [LawfulMinds W C Φ] [Cast C] [Perceives W C] (w : W) (p : P) (φs : List Φ) :
    Grows (C := C) (Φ := Φ) w (witness w p φs) := by
  unfold witness
  exact grows_foldl _ (fun w x => grows_foldl _ (fun w φ => Grows.trans (learn_grows _ _ _ _)
    (grows_foldl _ (fun w y => learnWith_grows _ _ _ _ _) _ _)) _ _) _ _

/-- Learning keeps a right record right: the present grows, the past and the record stay. -/
theorem grows_rec [Cast C] {w w' : W} (hg : Grows (C := C) (Φ := Φ) w w') (c : C)
    (h : RecOk (Φ := Φ) w c) : RecOk (Φ := Φ) w' c := by
  obtain ⟨hn, hc⟩ := hg
  obtain ⟨hs, X, hX, ha⟩ := hc c
  obtain ⟨B₁, B₂, hB, h₁, h₂, hr⟩ := h
  refine ⟨B₁, B₂ ++ X, by rw [hX, hB, List.append_assoc], fun h hh => by rw [hn]; exact h₁ h hh,
    fun h hh => ?_, fun m hm => hr m (by rw [← hs]; exact hm)⟩
  rw [hn]
  rcases List.mem_append.mp hh with hh | hh
  · exact h₂ h hh
  · exact ha h hh

/-- In the middle of an event too, `view` is `viewSpec`. -/
theorem view_eq_viewSpec_of_grows [Cast C] {w w' : W} (h : Rec (Φ := Φ) w)
    (hg : Grows (C := C) (Φ := Φ) w w') (c : C) : view w' c = viewSpec w' c :=
  view_eq_viewSpec_of_rec w' c (grows_rec hg c (h c))

/-! ### Recording, then the clock -/

/-- `c`'s record at `w` holds the views of `B`, up to repeats. -/
def RecHolds [Cast C] (w : W) (c : C) (B : List (Held C Φ)) : Prop :=
  ∀ m, HasMinds.settled w c = some m → c ∈ (Cast.all : List C) ∧ m.eraseDups = (pastHeads B).eraseDups

theorem pastHeads_of_nil (hr : Lore.rules (Φ := Φ) = []) (B : List (Held C Φ)) : pastHeads B = [] := by
  unfold pastHeads recordedHeads
  simp [hr]

theorem recordOne_frame [LawfulMinds W C Φ] (before w : W) (x : C) :
    Clock.now (recordOne before w x) = Clock.now w ∧ (∀ c, beliefs (recordOne before w x) c = beliefs w c) ∧
    (∀ c, c ≠ x → HasMinds.settled (recordOne before w x) c = HasMinds.settled w c) := by
  unfold recordOne
  simp only [recordedHeadsK_eq]
  split
  · exact ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
  · rename_i m hm
    split
    · exact ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
    · split
      · exact ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
      · exact ⟨LawfulMinds.now_setSettled _ _ _, fun c => LawfulMinds.beliefs_setSettled _ _ _ _,
          fun c hc => by rw [LawfulMinds.settled_setSettled w x c _ m hm]; simp [hc]⟩

/-- One character's turn: from a record of the past (or already of the present), a
record of the present. It may skip only a character with nothing about the present
(`hskip`). -/
theorem recordOne_done [LawfulMinds W C Φ] [Cast C] (before w : W) (x : C) (B₁ B₂ : List (Held C Φ))
    (hB : (beliefs w x).map Held.plain = B₁ ++ B₂) (h₁ : ∀ h ∈ B₁, h.about < Clock.now w)
    (h₂ : ∀ h ∈ B₂, h.about = Clock.now w)
    (hskip : ((beliefs w x).isEmpty || (decide (beliefs before x = beliefs w x) && Clock.now w != 0)) = true →
      B₂ = [])
    (hx : RecHolds w x B₁ ∨ RecHolds w x (B₁ ++ B₂)) :
    RecHolds (recordOne before w x) x (B₁ ++ B₂) := by
  intro m' hm'
  unfold recordOne at hm'
  simp only [recordedHeadsK_eq] at hm'
  cases hs : HasMinds.settled w x with
  | none => simp only [hs] at hm'; cases hm'
  | some m =>
    have hmem : x ∈ (Cast.all : List C) ∧ (m.eraseDups = (pastHeads B₁).eraseDups ∨
        m.eraseDups = (pastHeads (B₁ ++ B₂)).eraseDups) := by
      rcases hx with hx | hx
      · exact ⟨(hx m hs).1, Or.inl (hx m hs).2⟩
      · exact ⟨(hx m hs).1, Or.inr (hx m hs).2⟩
    refine ⟨hmem.1, ?_⟩
    simp only [hs] at hm'
    have hR : recordedHeads (beliefs w x) = recordedHeads (B₁ ++ B₂) := by
      rw [← hB, recordedHeads_map_plain]
    by_cases hsk : ((beliefs w x).isEmpty || (decide (beliefs before x = beliefs w x) && Clock.now w != 0)) = true
    · simp only [hsk, ↓reduceIte, hs, Option.some.injEq] at hm'
      subst hm'
      rcases hmem.2 with hpre | hdone
      · rw [hpre, hskip hsk, List.append_nil]
      · exact hdone
    · have hne : B₁ ++ B₂ ≠ [] := by
        rw [← hB]; intro h0
        apply hsk
        rw [List.map_eq_nil_iff.mp h0]; rfl
      have hm'eq : m'.eraseDups = (m ++ recordedHeads (beliefs w x)).eraseDups := by
        simp only [hsk, Bool.false_eq_true, ↓reduceIte] at hm'
        generalize hF : (recordedHeads (beliefs w x)).filter (!m.contains ·) = F at hm'
        cases F with
        | nil =>
          simp only [hs] at hm'; cases hm'
          rw [← eraseDups_append_new, hF, List.append_nil]
        | cons y ys =>
          simp only [] at hm'
          rw [LawfulMinds.settled_setSettled w x x _ m hs] at hm'
          simp only [↓reduceIte, Option.some.injEq] at hm'
          subst hm'
          rw [← hF]; exact eraseDups_append_new _ _
      rw [hm'eq, hR]
      rcases hmem.2 with hpre | hdone
      · rw [eraseDups_append_congr _ hpre, pastHeads_present B₁ B₂ _ h₁ h₂ hne]
      · rw [eraseDups_append_congr _ hdone,
          eraseDups_append_of_sub _ _ (recordedHeads_sub_pastHeads _ hne)]

/-- Before the loop's turn for `c`: `c`'s base (fixed by the loop) is the past then the
present, and the record holds the past or already the present. -/
def RecPre [Cast C] (w₀ w : W) (c : C) : Prop :=
  ∃ B₁ B₂ : List (Held C Φ), (beliefs w₀ c).map Held.plain = B₁ ++ B₂ ∧
    (∀ h ∈ B₁, h.about < Clock.now w₀) ∧ (∀ h ∈ B₂, h.about = Clock.now w₀) ∧
    (RecHolds w c B₁ ∨ RecHolds w c (B₁ ++ B₂))

theorem recHolds_congr [Cast C] {w w' : W} {c : C} (B : List (Held C Φ))
    (hs : HasMinds.settled w' c = HasMinds.settled w c) (h : RecHolds w c B) : RecHolds w' c B :=
  fun m hm => h m (by rw [← hs]; exact hm)

theorem foldl_recordOne [LawfulMinds W C Φ] [Cast C] (before w₀ : W)
    (hskip : ∀ c, ((beliefs w₀ c).isEmpty || (decide (beliefs before c = beliefs w₀ c) &&
      Clock.now w₀ != 0)) = true → ∀ h ∈ beliefs w₀ c, h.about < Clock.now w₀) : ∀ (l : List C) (w : W),
    Clock.now w = Clock.now w₀ → (∀ c, beliefs w c = beliefs w₀ c) → (∀ c, RecPre (Φ := Φ) w₀ w c) →
    Clock.now (l.foldl (recordOne before) w) = Clock.now w₀ ∧
    (∀ c, beliefs (l.foldl (recordOne before) w) c = beliefs w₀ c) ∧
    (∀ c, RecPre (Φ := Φ) w₀ (l.foldl (recordOne before) w) c) ∧
    ∀ c, (RecHolds w c ((beliefs w₀ c).map Held.plain) ∨ c ∈ l) →
      RecHolds (l.foldl (recordOne before) w) c ((beliefs w₀ c).map Held.plain)
  | [], w, hn, hb, hp => ⟨hn, hb, hp, fun c hc => by
      rcases hc with hc | hc
      · exact hc
      · cases hc⟩
  | x :: l, w, hn, hb, hp => by
    obtain ⟨hn', hb', hs'⟩ := recordOne_frame before w x
    -- the turn for `x` records the present for `x`
    have hx : RecHolds (recordOne before w x) x ((beliefs w₀ x).map Held.plain) := by
      obtain ⟨B₁, B₂, hB, h₁, h₂, hr⟩ := hp x
      rw [hB]
      refine recordOne_done before w x B₁ B₂ (by rw [hb]; exact hB) (by rw [hn]; exact h₁)
        (by rw [hn]; exact h₂) (fun hsk => ?_) hr
      rw [hb, hn] at hsk
      have hlt := hskip x hsk
      cases B₂ with
      | nil => rfl
      | cons y ys =>
        exfalso
        have : y ∈ (beliefs w₀ x).map Held.plain := by rw [hB]; simp
        obtain ⟨h, hh, hy⟩ := List.mem_map.mp this
        have := hlt h hh
        have hyn := h₂ y (by simp)
        rw [← hy] at hyn
        simp only [Held.plain] at hyn
        omega
    have hp' : ∀ c, RecPre (Φ := Φ) w₀ (recordOne before w x) c := by
      intro c
      obtain ⟨B₁, B₂, hB, h₁, h₂, hr⟩ := hp c
      refine ⟨B₁, B₂, hB, h₁, h₂, ?_⟩
      by_cases hc : c = x
      · subst hc; rw [hB] at hx; exact Or.inr hx
      · rcases hr with hr | hr
        · exact Or.inl (recHolds_congr _ (hs' c hc) hr)
        · exact Or.inr (recHolds_congr _ (hs' c hc) hr)
    obtain ⟨ihn, ihb, ihp, ihd⟩ := foldl_recordOne before w₀ hskip l (recordOne before w x) (by rw [hn', hn])
      (fun c => by rw [hb' c, hb c]) hp'
    refine ⟨ihn, ihb, ihp, fun c hc => ihd c ?_⟩
    by_cases hcx : c = x
    · subst hcx; exact Or.inl hx
    · rcases hc with hc | hc
      · exact Or.inl (recHolds_congr _ (hs' c hcx) hc)
      · rcases List.mem_cons.mp hc with hc | hc
        · exact absurd hc hcx
        · exact Or.inr hc

/-- Between events: the records are right, and after the first event nothing is about
the present yet (the clock has just moved on). -/
def RecAt [Cast C] (w : W) : Prop :=
  Rec (Φ := Φ) w ∧ (Clock.now w = 0 ∨ ∀ c : C, ∀ h ∈ beliefs w c, h.about < Clock.now w)

/-- Recording at the end of an event, then moving the clock on, keeps the records right:
the present becomes the past, and its views are now in the record. A character
`recordSettled` skips (an unchanged base after the first event) has nothing about the
present (`hskip`). -/
theorem rec_recordSettled_tick [LawfulMinds W C Φ] [Cast C] (before w : W) (h : Rec (Φ := Φ) w)
    (hskip : ∀ c, beliefs before c = beliefs w c → Clock.now w ≠ 0 →
      ∀ h ∈ beliefs w c, h.about < Clock.now w) :
    RecAt (Φ := Φ) (Clock.tick (recordSettled before w)) := by
  have hdone : Clock.now (recordSettled before w) = Clock.now w ∧
      (∀ c, beliefs (recordSettled before w) c = beliefs w c) ∧
      ∀ c, RecHolds (recordSettled before w) c ((beliefs w c).map Held.plain) := by
    unfold recordSettled
    split
    · rename_i he
      refine ⟨rfl, fun _ => rfl, fun c m hm => ?_⟩
      obtain ⟨B₁, B₂, _, _, _, hr⟩ := h c
      have hr0 := List.isEmpty_iff.mp he
      rw [(hr m hm).2, pastHeads_of_nil hr0, pastHeads_of_nil hr0]
      exact ⟨(hr m hm).1, rfl⟩
    · have hp : ∀ c, RecPre (Φ := Φ) w w c := by
        intro c
        obtain ⟨B₁, B₂, hB, h₁, h₂, hr⟩ := h c
        exact ⟨B₁, B₂, hB, h₁, h₂, Or.inl hr⟩
      have hsk : ∀ c, ((beliefs w c).isEmpty || (decide (beliefs before c = beliefs w c) &&
          Clock.now w != 0)) = true → ∀ h ∈ beliefs w c, h.about < Clock.now w := by
        intro c hc x hx
        rcases Bool.or_eq_true _ _ ▸ hc with he | hu
        · rw [List.isEmpty_iff.mp he] at hx; cases hx
        · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hu
          exact hskip c hu.1 hu.2 x hx
      obtain ⟨hn, hb, hpre, hd⟩ := foldl_recordOne before w hsk Cast.all w rfl (fun _ => rfl) hp
      refine ⟨hn, hb, fun c => ?_⟩
      by_cases hc : c ∈ (Cast.all : List C)
      · exact hd c (Or.inr hc)
      · -- nobody outside the cast keeps a record
        intro m hm
        obtain ⟨B₁, B₂, _, _, _, hr⟩ := hpre c
        rcases hr with hr | hr
        · exact absurd (hr m hm).1 hc
        · exact absurd (hr m hm).1 hc
  obtain ⟨hn, hb, hd⟩ := hdone
  have hle : ∀ c, ∀ x ∈ (beliefs w c).map Held.plain, x.about ≤ Clock.now w := by
    intro c x hx
    obtain ⟨B₁, B₂, hB, h₁, h₂, _⟩ := h c
    rw [hB] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Nat.le_of_lt (h₁ x hx)
    · exact Nat.le_of_eq (h₂ x hx)
  have hlt := LawfulMinds.now_lt_tick (recordSettled before w)
  refine ⟨fun c => ?_, Or.inr fun c x hx => by
    rw [LawfulMinds.beliefs_tick, hb] at hx
    have := hle c (Held.plain x) (List.mem_map_of_mem hx)
    simp only [Held.plain] at this
    omega⟩
  refine ⟨(beliefs w c).map Held.plain, [], ?_, fun x hx => ?_, by simp, fun m hm => ?_⟩
  · rw [LawfulMinds.beliefs_tick, hb, List.append_nil]
  · have := hle c x hx
    omega
  · rw [LawfulMinds.settled_tick] at hm
    exact hd c m hm

/-- One event keeps the records right, if the event's step only learns. -/
theorem rec_next [LawfulMinds W C Φ] [Cast C] [Perceives W C] {E : Type} [Domain W E]
    [Observable W E Φ P] [Invariant W] (hstep : ∀ (w : W) (e : E), Grows (C := C) (Φ := Φ) w (Domain.step w e))
    (w : W) (e : E) (h : RecAt (Φ := Φ) w) : RecAt (Φ := Φ) (next w e) := by
  show RecAt (Clock.tick (recordSettled w (match Observable.seen w e with
    | some (p, φs) => witness (Domain.step w e) p φs
    | none => Domain.step w e)))
  have hg : Grows (C := C) (Φ := Φ) w (match Observable.seen w e with
      | some (p, φs) => witness (Domain.step w e) p φs
      | none => Domain.step w e) := by
    refine Grows.trans (hstep w e) ?_
    split
    · exact witness_grows _ _ _
    · exact Grows.refl _
  apply rec_recordSettled_tick _ _ (fun c => grows_rec hg c (h.1 c))
  intro c hb hn x hx
  rw [hg.1] at hn ⊢
  rw [← hb] at hx
  rcases h.2 with h0 | hlt
  · exact absurd h0 hn
  · exact hlt c x hx

theorem rec_run [LawfulMinds W C Φ] [Cast C] [Perceives W C] {E : Type} [Domain W E]
    [Observable W E Φ P] [Invariant W] (hstep : ∀ (w : W) (e : E), Grows (C := C) (Φ := Φ) w (Domain.step w e)) :
    ∀ (w : W) (es : List E), RecAt (Φ := Φ) w → RecAt (Φ := Φ) (run w es)
  | _, [], h => h
  | w, e :: es, h => rec_run hstep (next w e) es (rec_next hstep w e h)

/-- L5 is exact: along any story from a world whose records are right (between
events), every state's `view` is `viewSpec`. -/
theorem view_run [LawfulMinds W C Φ] [Cast C] [Perceives W C] {E : Type} [Domain W E]
    [Observable W E Φ P] [Invariant W] (hstep : ∀ (w : W) (e : E), Grows (C := C) (Φ := Φ) w (Domain.step w e))
    (w : W) (h : RecAt (Φ := Φ) w) (es : List E) (c : C) : view (run w es) c = viewSpec (run w es) c :=
  view_eq_viewSpec_of_rec _ c ((rec_run hstep w es h).1 c)

end Record

end LangLib.World
