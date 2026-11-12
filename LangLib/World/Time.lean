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

/-! ## Durations

Metric constraints, in whatever unit the story uses (minutes, say):
"the talk lasted twenty to forty minutes" is `dur i 20 40`; "an hour later"
is `gap i j 55 65` (from the end of `i` to the start of `j`). -/

inductive Metric
  /-- event `i` lasts between `lo` and `hi` -/
  | dur (i lo hi : Nat)
  /-- event `j` starts between `lo` and `hi` after event `i` ends -/
  | gap (i j lo hi : Nat)
  deriving DecidableEq, Repr

def Metric.sat (t : Timeline) : Metric → Bool
  | .dur i lo hi => match t.get? i with
    | some a => lo ≤ a.e - a.s && a.e - a.s ≤ hi
    | none => false
  | .gap i j lo hi => match t.get? i, t.get? j with
    | some a, some b => a.e ≤ b.s && lo ≤ b.s - a.e && b.s - a.e ≤ hi
    | _, _ => false

/-! ## Finding a timeline

An untrusted solver: each Allen relation and metric constraint is a conjunction
of difference constraints `x_b - x_a ≥ w` on endpoints (a simple temporal
problem); disjunctions are searched depth first, and each choice is checked for
feasibility by Bellman–Ford (longest paths from 0). Whatever it returns is
re-checked by `Timeline.Satisfies` and `Metric.sat`, so it needs no proof. -/

/-- `(a, b, w)`: endpoint `b` is at least `w` after endpoint `a`
(endpoint `2i` is the start of event `i`, `2i+1` its end). -/
abbrev Diff := Nat × Nat × Int

private def S (i : Nat) : Nat := 2 * i
private def E (i : Nat) : Nat := 2 * i + 1

private def eq2 (a b : Nat) : List Diff := [(a, b, 0), (b, a, 0)]

/-- Difference constraints for `r i j`. -/
def Allen.diffs (i j : Nat) : Allen → List Diff
  | .before => [(E i, S j, 1)]
  | .meets => eq2 (E i) (S j)
  | .overlaps => [(S i, S j, 1), (S j, E i, 1), (E i, E j, 1)]
  | .starts => eq2 (S i) (S j) ++ [(E i, E j, 1)]
  | .during => [(S j, S i, 1), (E i, E j, 1)]
  | .finishes => [(S j, S i, 1)] ++ eq2 (E i) (E j)
  | .equal => eq2 (S i) (S j) ++ eq2 (E i) (E j)
  | .finishedBy => [(S i, S j, 1)] ++ eq2 (E i) (E j)
  | .contains => [(S i, S j, 1), (E j, E i, 1)]
  | .startedBy => eq2 (S i) (S j) ++ [(E j, E i, 1)]
  | .overlappedBy => [(S j, S i, 1), (S i, E j, 1), (E j, E i, 1)]
  | .metBy => eq2 (E j) (S i)
  | .after => [(E j, S i, 1)]

def Metric.diffs : Metric → List Diff
  | .dur i lo hi => [(S i, E i, lo), (E i, S i, -(hi : Int))]
  | .gap i j lo hi => [(E i, S j, lo), (S j, E i, -(hi : Int))]

private def relax (ds : List Diff) (x : List Int) : List Int :=
  ds.foldl (fun x (a, b, w) =>
    let cand := x.getD a 0 + w
    if cand > x.getD b 0 then x.set b cand else x) x

/-- Least non-negative solution, or `none` if the constraints are infeasible. -/
def solveDiffs (points : Nat) (ds : List Diff) : Option (List Int) :=
  let rec go : Nat → List Int → Option (List Int)
    | 0, x => if relax ds x == x then some x else none
    | n + 1, x => let x' := relax ds x; if x' == x then some x else go n x'
  go (points + 1) (List.replicate points 0)

/-- A timeline for `n` events meeting `cs` and `ms`, if the search finds one. -/
def solve (n : Nat) (cs : List Constraint) (ms : List Metric := []) : Option Timeline :=
  let base := (List.range n).map (fun i => (S i, E i, (1 : Int))) ++ ms.flatMap Metric.diffs
  let rec search : List Constraint → List Diff → Option (List Int)
    | [], ds => solveDiffs (2 * n) ds
    | c :: rest, ds => c.rels.findSome? fun r =>
        let ds' := ds ++ r.diffs c.i c.j
        (solveDiffs (2 * n) ds').bind fun _ => search rest ds'
  (search cs base).map fun x =>
    (List.range n).map fun i => ⟨(x.getD (S i) 0).toNat, (x.getD (E i) 0).toNat⟩


end LangLib.World
