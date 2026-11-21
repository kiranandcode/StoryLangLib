/-!
# List functions for the kernel

`decide +kernel` evaluates a closed term by reduction. Core's list functions are
defined by structural recursion, which compiles through `brecOn`: the kernel
unfolds the recursor's `below` tuple and the functional `_f` at every step. The
same functions written with `List.rec` directly reduce by one iota step per cons
cell, about two to three times as fast (`abstractions/ROUND-2.md`). Each is
proved equal to its core counterpart, and a `@[csimp]` lemma makes compiled code
run the core one: these are kernel encodings, not new definitions.

`Nat.beq`, `Nat.blt`, `Nat.ble` and the bit operations are reduced by the kernel
as single steps on literals (GMP), unlike `==` on `Nat`, which goes through
`instBEqOfDecidableEq`, `Nat.decEq` and `decide`.
-/

namespace LangLib.World.K

universe u v

noncomputable def all {α : Type u} (l : List α) (p : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ r => p a && r) l

noncomputable def any {α : Type u} (l : List α) (p : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => p a || r) l

noncomputable def filter {α : Type u} (p : α → Bool) (l : List α) : List α :=
  List.rec (motive := fun _ => List α) [] (fun a _ r => if p a then a :: r else r) l

noncomputable def filterMap {α : Type u} {β : Type v} (f : α → Option β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun a _ r => match f a with | some b => b :: r | none => r) l

noncomputable def foldl {α : Type u} {β : Type v} (f : α → β → α) (init : α) (l : List β) : α :=
  List.rec (motive := fun _ => α → α) (fun a => a) (fun b _ r a => r (f a b)) l init

noncomputable def append {α : Type u} (l m : List α) : List α :=
  List.rec (motive := fun _ => List α) m (fun a _ r => a :: r) l

/-- `insertBy` (`Domain.lean`), by its recursor. -/
noncomputable def insertBy {α : Type} (le : α → α → Bool) (x : α) (l : List α) : List α :=
  List.rec (motive := fun _ => List α) [x] (fun y ys r => if le x y then x :: y :: ys else y :: r) l

noncomputable def sortBy {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  List.rec (motive := fun _ => List α) [] (fun x _ r => insertBy le x r) l

@[csimp] theorem all_eq : @all = @List.all := by
  funext α l p; induction l with
  | nil => rfl
  | cons a l ih => show (p a && all l p) = (p a && l.all p); rw [ih]

@[csimp] theorem any_eq : @any = @List.any := by
  funext α l p; induction l with
  | nil => rfl
  | cons a l ih => show (p a || any l p) = (p a || l.any p); rw [ih]

@[csimp] theorem filter_eq : @filter = @List.filter := by
  funext α p l; induction l with
  | nil => rfl
  | cons a l ih =>
    show (if p a then a :: filter p l else filter p l) = List.filter p (a :: l)
    rw [ih, List.filter_cons]

@[csimp] theorem filterMap_eq : @filterMap = @List.filterMap := by
  funext α β f l; induction l with
  | nil => rfl
  | cons a l ih =>
    show (match f a with | some b => b :: filterMap f l | none => filterMap f l) = List.filterMap f (a :: l)
    rw [ih, List.filterMap_cons]; cases f a <;> rfl

@[csimp] theorem foldl_eq : @foldl = @List.foldl := by
  funext α β f init l
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => exact ih (f init a)

@[csimp] theorem append_eq : @append = @List.append := by
  funext α l m; induction l with
  | nil => rfl
  | cons a l ih => show a :: append l m = a :: List.append l m; rw [ih]

end LangLib.World.K
