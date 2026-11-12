import LangLib.World.Space

/-!
# Minds: beliefs, observation, telling and lying

Each character holds a list of beliefs. A belief is a fact (`atom φ`), its
denial (`neg φ`), or a belief about someone else's belief (`bel c b`), so
"Kiran thinks Marcus knows the letter is in the office" is
`bel marcus (atom (letter in office))` in Kiran's list.

* Observation (`Perceive`): after any event that is `Observable`, everyone
  present learns what it showed, and that each other witness saw it too.
* `tell` is said aloud: everyone present hears it. `whisper` reaches only the
  listener. Both require the speaker to believe what they say; `lie` requires
  that they do not.
* Learning a fact drops beliefs it supersedes (`Supersedes`), so a character
  who did not see the letter move keeps believing where it was: a false
  belief, which `falseBelief` detects and a story can use as dramatic irony.
-/

namespace LangLib.World

inductive Belief (C Φ : Type) where
  | atom (φ : Φ)
  | neg (φ : Φ)
  | bel (c : C) (b : Belief C Φ)
  deriving DecidableEq, Repr

class HasMinds (W : Type) (C Φ : outParam Type) where
  beliefs : W → C → List (Belief C Φ)
  setBeliefs : W → C → List (Belief C Φ) → W

inductive MindEv (C Φ : Type) where
  /-- said aloud: everyone present hears -/
  | tell (c d : C) (φ : Φ)
  /-- only `d` hears -/
  | whisper (c d : C) (φ : Φ)
  /-- `c` says what they do not believe -/
  | lie (c d : C) (φ : Φ)
  deriving DecidableEq, Repr

variable {W C P Φ : Type} [DecidableEq C] [DecidableEq P] [DecidableEq Φ]
  [HasLoc W C P] [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ]

open HasLoc HasMinds

def believes (w : W) (c : C) (b : Belief C Φ) : Bool := (beliefs w c).contains b

/-- `c` believes `φ` and it is true. -/
def knows (w : W) (c : C) (φ : Φ) : Bool := believes w c (.atom φ) && Truth.truth w φ

/-- `c` believes `φ` but it is false. -/
def falseBelief (w : W) (c : C) (φ : Φ) : Bool := believes w c (.atom φ) && !Truth.truth w φ

private def obsolete (new old : Belief C Φ) : Bool :=
  match new, old with
  | .atom φ, .atom ψ => φ != ψ && Supersedes.supersedes φ ψ
  | .atom φ, .neg ψ => φ == ψ
  | .neg φ, .atom ψ => φ == ψ
  | .bel c b, .bel c' b' => c == c' && obsolete b b'
  | _, _ => false

/-- `c` comes to believe `b`, dropping beliefs it makes obsolete. -/
def learn (w : W) (c : C) (b : Belief C Φ) : W :=
  setBeliefs w c (b :: (beliefs w c).filter fun old => old != b && !obsolete b old)

def learnAll (w : W) (c : C) (bs : List (Belief C Φ)) : W := bs.foldl (learn · c) w

/-- Everyone at `p` sees `φs`, and sees the others see them. -/
def witness [Cast C] (w : W) (p : P) (φs : List Φ) : W :=
  let present := Cast.all.filter fun x => loc w x == p
  present.foldl (fun w x =>
    learnAll w x (φs.flatMap fun φ =>
      .atom φ :: (present.filter (· != x)).map fun y => .bel y (.atom φ))) w

instance [Cast C] : Domain W (MindEv C Φ) where
  ok w
    | .tell c d φ | .whisper c d φ => loc w c == loc w d && believes w c (.atom φ)
    | .lie c d φ => loc w c == loc w d && !believes w c (.atom φ)
  step w
    | .tell c d φ =>
      learnAll (witness w (loc w c) [φ]) c [.bel d (.atom φ)]
    | .whisper c d φ =>
      learnAll (learnAll w d [.atom φ, .bel c (.atom φ)]) c [.bel d (.atom φ)]
    | .lie c d φ =>
      learnAll (learnAll w d [.atom φ, .bel c (.atom φ)]) c [.bel d (.atom φ)]
  why w
    | .tell c d φ | .whisper c d φ =>
      if loc w c != loc w d then "they are not together" else "the speaker does not know that"
    | .lie c d _ => if loc w c != loc w d then "they are not together" else "the speaker believes it, so it is not a lie"

/-- Witnessing: after each event, those present learn what it showed. -/
instance {E : Type} [Cast C] [Observable W E Φ P] : Perceive W E where
  perceive before e after :=
    match Observable.seen before e with
    | some (p, φs) => witness after p φs
    | none => after

end LangLib.World
