import LangLib.World.Goals

/-!
# Cause

When does the story bear out a "because"? This module gives causation as
counterfactual dependence along the story (Lewis; Halpern and Pearl's
"but-for" test, specialised to a sequence of events): `A` causes `B` if `B`
holds in the story and would not with `A` taken out. Three things can depend
on an earlier event:

* **What makes an event possible** (`enables`): event `j` is allowed where it
  stands, and with event `i` removed it is not. The moon on the judge enables
  the blast; the antenna in a copy enables the bomb it carries.
* **Why an event is done** (`motivates`): event `j` is explained by its
  agent's goal or plan (`Goals.motives`), and with event `i` removed it is not,
  so `i` gave the reason (adopting the goal, starting the plan, a promise).
* **What holds** (`bringsAbout`): a property of the state holds at a point,
  and with event `i` removed it does not.

A fact can also be the reason for an act (its agent believed it when acting:
checked by the minds module at the point of the act), and one fact the cause
of another when a lore rule derives the second from the first (`loreCause`).

Removing an event and replaying is exact, decidable and cheap for stories of
this size; the text's "because" is then a claim the model can refuse.
-/

namespace LangLib.World

section
variable {W E : Type} [Domain W E] [Perceive W E] [Invariant W] [Clock W]

/-- Event `j` of `es` is allowed where it stands. -/
def okAt (w : W) (es : List E) (j : Nat) : Bool :=
  match es[j]? with
  | some e => Domain.ok (run w (es.take j)) e
  | none => false

/-- Event `i` makes event `j` possible: `j` is allowed, and with `i` taken out
of the story it is not. -/
def enables (w : W) (es : List E) (i j : Nat) : Bool :=
  i < j && okAt w es j && !okAt w (es.eraseIdx i) (j - 1)

/-- Event `i` brings about `p` at point `k` (after the first `k` events): `p`
holds there, and with `i` taken out it does not. -/
def bringsAbout (w : W) (es : List E) (i k : Nat) (p : W → Bool) : Bool :=
  i < k && p (run w (es.take k)) && !p (run w ((es.eraseIdx i).take (k - 1)))
end

section
variable {W C Φ E S : Type} [DecidableEq C] [DecidableEq Φ] [DecidableEq E] [HasGoals W C Φ E]
  [HasDialogue W C Φ] [Domain W S] [Perceive W S] [Invariant W] [Clock W] [Purpose W S C Φ]
  [Inject (GoalEv C Φ E) S] [Inject E S] [DecidableEq S]

/-- Event `j` of `es` is done for a reason: a plan step or a goal of its agent. -/
def motivatedAt (w : W) (es : List S) (j : Nat) : Bool :=
  match ((motives (C := C) (Φ := Φ) (E := E) w es 0).find? (·.1 == j)).map (·.2) with
  | some (Motive.step _ _) | some (Motive.goal _ _) => true
  | _ => false

/-- Event `i` gives event `j` its reason: `j` is motivated, and with `i` taken
out it is not. -/
def motivates (w : W) (es : List S) (i j : Nat) : Bool :=
  i < j && motivatedAt (C := C) (Φ := Φ) (E := E) w es j &&
    !motivatedAt (C := C) (Φ := Φ) (E := E) w (es.eraseIdx i) (j - 1)
end

/-- The lore derives `b` from premises that include `a`. -/
def loreCause {Φ : Type} [DecidableEq Φ] [Lore Φ] (a b : Φ × Bool) : Bool :=
  (Lore.rules (Φ := Φ)).any fun r => r.head == b && r.body.contains a

end LangLib.World
