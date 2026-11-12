/-!
# Interval time

Events occupy intervals of story time (the *fabula*), which need not match the
order in which the text tells them (the *syuzhet*: flashbacks, "meanwhile").
Qualitative relations between intervals are Allen's thirteen; a story states
some of them, and a concrete assignment of endpoints is the certificate that
they are consistent.

* `Allen.Holds r a b`: relation `r` holds between intervals `a` and `b`;
* `Interval.rel a b`: the relation that does hold, with `rel_holds` and
  `holds_unique`, so the thirteen relations are jointly exhaustive and pairwise
  disjoint;
* `Timeline.Satisfies`: an endpoint assignment meets a list of (disjunctive)
  constraints; it is decidable, so consistency is proved by `decide`.
-/

namespace LangLib.World

structure Interval where
  s : Nat
  e : Nat
  deriving DecidableEq, Repr

/-- A proper interval starts before it ends. -/
def Interval.Proper (i : Interval) : Prop := i.s < i.e

instance (i : Interval) : Decidable i.Proper := inferInstanceAs (Decidable (i.s < i.e))

inductive Allen
  | before | meets | overlaps | starts | during | finishes | equal
  | finishedBy | contains | startedBy | overlappedBy | metBy | after
  deriving DecidableEq, Repr

namespace Allen

def all : List Allen :=
  [before, meets, overlaps, starts, during, finishes, equal,
   finishedBy, contains, startedBy, overlappedBy, metBy, after]

/-- The endpoint definition of each relation. -/
def Holds : Allen → Interval → Interval → Prop
  | before, a, b => a.e < b.s
  | meets, a, b => a.e = b.s
  | overlaps, a, b => a.s < b.s ∧ b.s < a.e ∧ a.e < b.e
  | starts, a, b => a.s = b.s ∧ a.e < b.e
  | during, a, b => b.s < a.s ∧ a.e < b.e
  | finishes, a, b => b.s < a.s ∧ a.e = b.e
  | equal, a, b => a.s = b.s ∧ a.e = b.e
  | finishedBy, a, b => a.s < b.s ∧ a.e = b.e
  | contains, a, b => a.s < b.s ∧ b.e < a.e
  | startedBy, a, b => a.s = b.s ∧ b.e < a.e
  | overlappedBy, a, b => b.s < a.s ∧ a.s < b.e ∧ b.e < a.e
  | metBy, a, b => b.e = a.s
  | after, a, b => b.e < a.s

instance (r : Allen) (a b : Interval) : Decidable (r.Holds a b) := by
  cases r <;> unfold Holds <;> infer_instance

/-- The converse relation. -/
def inv : Allen → Allen
  | before => after | meets => metBy | overlaps => overlappedBy | starts => startedBy
  | during => contains | finishes => finishedBy | equal => equal
  | finishedBy => finishes | contains => during | startedBy => starts
  | overlappedBy => overlaps | metBy => meets | after => before

theorem holds_inv (r : Allen) (a b : Interval) : r.Holds a b ↔ r.inv.Holds b a := by
  cases r <;> simp only [Holds, inv] <;> omega

end Allen

/-- The relation that holds between two proper intervals. -/
def Interval.rel (a b : Interval) : Allen :=
  if a.e < b.s then .before
  else if a.e = b.s then .meets
  else if b.e < a.s then .after
  else if b.e = a.s then .metBy
  else if a.s = b.s then
    (if a.e < b.e then .starts else if a.e = b.e then .equal else .startedBy)
  else if a.s < b.s then
    (if a.e < b.e then .overlaps else if a.e = b.e then .finishedBy else .contains)
  else
    (if a.e < b.e then .during else if a.e = b.e then .finishes else .overlappedBy)

/-- Exhaustive: some relation always holds. -/
theorem Interval.rel_holds (a b : Interval) (ha : a.Proper) (hb : b.Proper) :
    (a.rel b).Holds a b := by
  unfold Interval.Proper at ha hb
  unfold Interval.rel
  repeat' split
  all_goals simp only [Allen.Holds]; omega

/-- Disjoint: at most one relation holds. -/
theorem Allen.holds_unique {r r' : Allen} {a b : Interval} (ha : a.Proper) (hb : b.Proper)
    (h : r.Holds a b) (h' : r'.Holds a b) : r = r' := by
  unfold Interval.Proper at ha hb
  cases r <;> cases r' <;> simp only [Allen.Holds] at h h' <;> first | rfl | omega

/-! ## Timelines -/

/-- `i` stands in one of `rels` to `j` (events named by number). -/
structure Constraint where
  i : Nat
  rels : List Allen
  j : Nat
  deriving DecidableEq, Repr

/-- An endpoint assignment for events `0 … n-1`. -/
abbrev Timeline := List Interval

def Timeline.get? (t : Timeline) (i : Nat) : Option Interval := t[i]?

def Constraint.Sat (t : Timeline) (c : Constraint) : Prop :=
  ∃ a b, t.get? c.i = some a ∧ t.get? c.j = some b ∧ ∃ r ∈ c.rels, r.Holds a b

instance (t : Timeline) (c : Constraint) : Decidable (c.Sat t) :=
  match h₁ : t.get? c.i, h₂ : t.get? c.j with
  | some a, some b =>
    if hr : ∃ r ∈ c.rels, r.Holds a b then
      isTrue ⟨a, b, h₁, h₂, hr⟩
    else isFalse fun ⟨a', b', h₁', h₂', hr'⟩ => by
      rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'; exact hr hr'
  | none, _ => isFalse fun ⟨_, _, h, _⟩ => by rw [h₁] at h; cases h
  | some _, none => isFalse fun ⟨_, _, _, h, _⟩ => by rw [h₂] at h; cases h

/-- Every interval is proper and every constraint holds. -/
def Timeline.Satisfies (t : Timeline) (cs : List Constraint) : Prop :=
  (∀ i ∈ t, i.Proper) ∧ ∀ c ∈ cs, c.Sat t

instance (t : Timeline) (cs : List Constraint) : Decidable (t.Satisfies cs) := by
  unfold Timeline.Satisfies; infer_instance

/-- Constraints are consistent if some timeline satisfies them. -/
def Consistent (n : Nat) (cs : List Constraint) : Prop :=
  ∃ t : Timeline, t.length = n ∧ t.Satisfies cs


end LangLib.World
