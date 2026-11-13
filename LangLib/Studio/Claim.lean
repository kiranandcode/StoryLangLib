import LangLib.Studio.Parse

/-!
# Claims: what a paragraph says the state is

The post hoc workflow reads higher-level facts off each paragraph (who now
believes what, who is where, who has consented to what) and asks whether the
events imply them. A claim is checked against the state after the paragraph;
as data it can be stated in a story's Lean file and proved by `decide`.

```
thinks mara noteForMara        falseBelief mara noteForMara   knows kiran noteForKiran
unaware theo maraReadNote      thinksThinks kiran theo kiranLikesTheo
true theoLikesKiran            at theo roof                   holds mara note
consented kiran theo kiss      goal theo at(theo,roof)        bond kiran theo trust >= 2
```
-/

namespace LangLib.Studio
open LangLib.World

inductive Cmp | ge | le | eq | gt | lt
  deriving DecidableEq, Repr

def Cmp.eval : Cmp → Nat → Nat → Bool
  | .ge, x, y => x ≥ y | .le, x, y => x ≤ y | .eq, x, y => x == y
  | .gt, x, y => x > y | .lt, x, y => x < y

inductive Claim where
  | thinks (c : Nat) (l : Fact × Bool)
  | knows (c : Nat) (l : Fact × Bool)
  | falseBelief (c : Nat) (l : Fact × Bool)
  | unaware (c : Nat) (f : Fact)
  | thinksThinks (c d : Nat) (l : Fact × Bool)
  | holdsTrue (l : Fact × Bool)
  | consented (b a : Nat) (x : Act)
  | goal (c : Nat) (l : Fact × Bool)
  | bond (a b : Nat) (d : Dim) (op : Cmp) (n : Nat)
  deriving DecidableEq, Repr

variable {s : Spec}

def Claim.eval (w : W s) : Claim → Bool
  | .thinks c l => (view w (⟨c⟩ : Ch s)).contains (lit l)
  | .knows c l => (view w (⟨c⟩ : Ch s)).contains (lit l) && truthLit w (lit (s := s) l)
  | .falseBelief c l => (view w (⟨c⟩ : Ch s)).contains (lit l) && !truthLit w (lit (s := s) l)
  | .unaware c f =>
    let v : List (SFact s × Bool) := view w (⟨c⟩ : Ch s)
    !v.contains (⟨f⟩, true) && !v.contains (⟨f⟩, false)
  | .thinksThinks c d l => (viewOf w (⟨c⟩ : Ch s) ⟨d⟩).contains (lit l)
  | .holdsTrue l => truthLit w (lit (s := s) l)
  | .consented b a x => w.consent.contains (⟨b⟩, ⟨a⟩, x)
  | .goal c l => (goalsOf w (⟨c⟩ : Ch s)).contains (lit l)
  | .bond a b d op n => op.eval (HasBonds.bond w (⟨a⟩ : Ch s) ⟨b⟩ d) n

def Names.claim (n : Names) (str : String) : Except String Claim := do
  match (str.splitOn " ").filter (· != "") with
  | ["thinks", c, l] => return .thinks (← n.ch c) (← n.lit l)
  | ["knows", c, l] => return .knows (← n.ch c) (← n.lit l)
  | ["falseBelief", c, l] => return .falseBelief (← n.ch c) (← n.lit l)
  | ["unaware", c, f] => return .unaware (← n.ch c) (← n.fact f)
  | ["thinksThinks", c, d, l] => return .thinksThinks (← n.ch c) (← n.ch d) (← n.lit l)
  | ["true", l] => return .holdsTrue (← n.lit l)
  | ["at", c, p] => return .holdsTrue (.at_ (← n.ch c) (← n.pl p), true)
  | ["holds", c, o] => return .holdsTrue (.holds (← n.ch c) (← n.ob o), true)
  | ["consented", b, a, x] =>
    let some x := Act.ofString? x | throw s!"unknown act \"{x}\""
    return .consented (← n.ch b) (← n.ch a) x
  | ["goal", c, l] => return .goal (← n.ch c) (← n.lit l)
  | ["bond", a, b, d, op, v] =>
    let some d := Dim.ofString? d | throw s!"unknown dimension \"{d}\""
    let some v := v.toNat? | throw s!"not a number: {v}"
    let op ← match op with
      | ">=" => pure Cmp.ge | "<=" => pure .le | "==" | "=" => pure .eq
      | ">" => pure .gt | "<" => pure .lt | _ => throw s!"unknown comparison {op}"
    return .bond (← n.ch a) (← n.ch b) d op v
  | _ => throw s!"cannot read claim \"{str}\""

end LangLib.Studio
