import LangLib.World.Mind

/-!
# Mystery: detective fair play

A detective's conclusion is fair when it can be derived from the evidence the
detective holds at that moment, and a mystery is fair to its reader when what
the page has shown before a reveal is enough to derive the solution. This
module makes both checkable for any story with minds.

* **Evidence** is what a character holds in their mind (`Mind.view`): clues
  they saw, were told, or concluded earlier. A `clue c l e` puts `l` in `c`'s
  evidence base with evidence `e` (a perceptual clue must be true).
* **Deduction rules** (`Deduction`) are the inferences the genre allows,
  named, from literals to a literal. They are not lore: a mind does not draw
  them by itself; a character draws one by a `conclude` move, and only then
  holds the conclusion (as their own inference).
* **conclude c l**: allowed only if `l` is derivable from `c`'s evidence by the
  rules (forward chaining over what they hold now). The step records which rule
  gave it, and `c` comes to believe it (`inferred`). A conclusion need not be
  true (a derivable mistake is fair); the reader's reveal must be.
* **suspect c l p**: a credence of `p` percent, below certainty. Allowed only
  with a lead: a rule for `l` with at least one premise held, and `l` not
  already refuted. A suspicion is not a belief: the mind does not change.
* **reveal r l**: the text confirms `l` to the reader `r` (any character
  standing for the reader). Fair only if `l` is true and the reader can derive
  it from what the page has shown them (`clue r ...`) so far.

`fairB` checks a whole story; `valid_fair` proves that a valid story is fair
play, for any story whose events include these (`MysteryEvents`).
-/

namespace LangLib.World

structure Inference (Φ : Type) where
  name : String
  body : List (BLit Φ)
  head : BLit Φ

/-- The inferences a story's detectives (and its reader) may draw. -/
class Deduction (Φ : Type) where
  rules : List (Inference Φ)

instance (priority := low) {Φ : Type} : Deduction Φ := ⟨[]⟩

structure MysState (C Φ : Type) where
  /-- credences as they were set: who, about what, percent, at which story step -/
  cred : List (C × BLit Φ × Nat × Nat) := []
  /-- conclusions drawn: who, what, by which rule (index into `Deduction.rules`) -/
  concl : List (C × BLit Φ × Nat) := []
  /-- what the text has confirmed to its reader -/
  reveals : List (BLit Φ) := []
  deriving DecidableEq, Repr

class HasMystery (W : Type) (C Φ : outParam Type) where
  mys : W → MysState C Φ
  setMys : W → MysState C Φ → W

inductive MysEv (C Φ : Type) where
  | clue (c : C) (l : BLit Φ) (e : Evid C)
  | conclude (c : C) (l : BLit Φ)
  | suspect (c : C) (l : BLit Φ) (pct : Nat)
  | reveal (r : C) (l : BLit Φ)
  deriving DecidableEq, Repr

section
variable {W C P Φ : Type} [DecidableEq C] [DecidableEq P] [DecidableEq Φ]
  [HasLoc W C P] [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ] [Credence W C Φ]
  [Fluent Φ] [Clock W] [PartialLoc W C] [Deduction Φ] [HasMystery W C Φ]

/-- Forward chaining with the deduction rules from `held`: each derived literal
with the index of the rule that first gave it (bounded by the number of rules). -/
def deriveFrom (held : List (BLit Φ)) : List (BLit Φ × Nat) :=
  let rules := (Deduction.rules (Φ := Φ)).zip (List.range (Deduction.rules (Φ := Φ)).length)
  let step (acc : List (BLit Φ × Nat)) : List (BLit Φ × Nat) :=
    rules.foldl (fun acc (r, i) =>
      let have_ (l : BLit Φ) := held.contains l || acc.any (·.1 == l)
      if r.body.all have_ && !have_ r.head then acc ++ [(r.head, i)] else acc) acc
  let rec go : Nat → List (BLit Φ × Nat) → List (BLit Φ × Nat)
    | 0, acc => acc
    | n + 1, acc => go n (step acc)
  go ((Deduction.rules (Φ := Φ)).length + 1) []

/-- What `c` holds as evidence now. -/
def evidence (w : W) (c : C) : List (BLit Φ) := view w c

/-- How `c` gets `l` from what they hold: `some none` if they hold it already,
`some (some i)` if rule `i` derives it, `none` if they cannot. -/
def derivation (w : W) (c : C) (l : BLit Φ) : Option (Option Nat) :=
  let held := evidence w c
  if held.contains l then some none else
  ((deriveFrom held).find? (·.1 == l)).map fun (_, i) => some i

def derivable (w : W) (c : C) (l : BLit Φ) : Bool := (derivation w c l).isSome

def negLit (l : BLit Φ) : BLit Φ := (l.1, !l.2)

/-- A lead for `l`: a rule concluding it with at least one premise `c` holds or derives. -/
def lead (w : W) (c : C) (l : BLit Φ) : Bool :=
  let held := evidence w c
  let have_ (x : BLit Φ) := held.contains x || (deriveFrom held).any (·.1 == x)
  (Deduction.rules (Φ := Φ)).any fun r => r.head == l && r.body.any have_

/-- The rule for `l` that `c` is closest to, and the premises it still needs. -/
def missing (w : W) (c : C) (l : BLit Φ) : Option (String × List (BLit Φ)) :=
  let held := evidence w c
  let d := deriveFrom held
  let have_ (x : BLit Φ) := held.contains x || d.any (·.1 == x)
  let cands := (Deduction.rules (Φ := Φ)).filter (·.head == l)
  let best := cands.foldl (fun (b : Option (Inference Φ)) r => match b with
    | none => some r
    | some r' => if (r.body.filter (!have_ ·)).length < (r'.body.filter (!have_ ·)).length then some r else some r') none
  best.map fun r => (r.name, r.body.filter (!have_ ·))

def mysOk (w : W) : MysEv C Φ → Bool
  | .clue _ l e => !e.perceptual || truthLit w l
  | .conclude c l => derivable w c l
  | .suspect c l p => 0 < p && p < 100 && lead w c l && !derivable w c (negLit l)
  | .reveal r l => truthLit w l && derivable w r l

def mysStep (w : W) : MysEv C Φ → W
  | .clue c l e => learn w c (ofLit l) e
  | .conclude c l =>
    let m := HasMystery.mys w
    let i := ((derivation w c l).join).getD 0
    let w := HasMystery.setMys w { m with concl := m.concl ++ [(c, l, i)], cred := m.cred ++ [(c, l, 100, Clock.now w)] }
    learn w c (ofLit l) .inferred
  | .suspect c l p =>
    let m := HasMystery.mys w
    HasMystery.setMys w { m with cred := m.cred ++ [(c, l, p, Clock.now w)] }
  | .reveal _ l =>
    let m := HasMystery.mys w
    HasMystery.setMys w { m with reveals := m.reveals ++ [l] }

variable [Repr Φ]

private def litWords (l : BLit Φ) : String := (if l.2 then "" else "not ") ++ (((reprStr l.1).splitOn ".").getLast!.replace ")" "")

def needsWords (w : W) (c : C) (l : BLit Φ) : String :=
  match missing w c l with
  | some (name, ms) => s!" ({name} still needs: {", ".intercalate (ms.map litWords)})"
  | none => " (no rule concludes it)"

def mysWhy (w : W) : MysEv C Φ → String
  | .clue .. => "a perception must be of something true"
  | .conclude c l => "not derivable from what they hold: an authorial leap" ++ needsWords w c l
  | .suspect c l p =>
    if p == 0 || p ≥ 100 then "a suspicion is a credence strictly between 0 and 100"
    else if derivable w c (negLit l) then "they have already ruled it out"
    else "no lead: nothing they hold points to it" ++ needsWords w c l
  | .reveal r l =>
    if !truthLit w l then "the text confirms something false"
    else "unfair to the reader: the page has not shown enough to derive it" ++ needsWords w r l

instance : Domain W (MysEv C Φ) where
  ok := mysOk
  step := mysStep
  why := mysWhy

/-- `c`'s credence in `l` now (the last one set; 100 for a conclusion). -/
def credence (w : W) (c : C) (l : BLit Φ) : Option Nat :=
  ((HasMystery.mys w).cred.filter fun (c', l', _, _) => c' == c && l' == l).getLast?.map (·.2.2.1)

end

/-! ## Fair play over a whole story -/

section
variable {W C P Φ : Type} [DecidableEq C] [DecidableEq P] [DecidableEq Φ]
  [HasLoc W C P] [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ] [Credence W C Φ]
  [Fluent Φ] [Clock W] [PartialLoc W C] [Deduction Φ] [HasMystery W C Φ]

/-- A story's events, some of which are mystery moves checked as this module checks them. -/
class MysteryEvents (W : Type) (E : outParam Type) (C Φ : Type) [Domain W E] [DecidableEq C] [DecidableEq Φ]
    [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ] [Fluent Φ] [Clock W] [Deduction Φ]
    [HasMystery W C Φ] {P : Type} [DecidableEq P] [HasLoc W C P] [Credence W C Φ] [PartialLoc W C] where
  asMys : E → Option (MysEv C Φ)
  ok_eq : ∀ (w : W) (e : E) (m : MysEv C Φ), asMys e = some m → Domain.ok w e = mysOk w m

variable {E : Type} [Domain W E] [Perceive W E] [Invariant W]
  [MysteryEvents W E C Φ (P := P)]

/-- Every conclusion was derivable from what its detective held, and every
reveal from what the page had shown the reader (and true), at its point. -/
def fairB (w : W) : List E → Bool
  | [] => true
  | e :: es =>
    (match MysteryEvents.asMys (W := W) (C := C) (Φ := Φ) (P := P) e with
     | some (.conclude c l) => derivable w c l
     | some (.reveal r l) => derivable w r l && truthLit w l
     | _ => true) && fairB (next w e) es

/-- A valid story is fair play: no detective concludes, and no page reveals,
what the evidence held at that moment does not derive. -/
theorem valid_fair : ∀ (w : W) (es : List E), Valid w es → fairB (C := C) (Φ := Φ) (P := P) w es = true
  | _, [], _ => rfl
  | w, e :: es, .cons h₁ _ h₃ => by
    unfold fairB
    rw [valid_fair _ es h₃, Bool.and_true]
    split
    · rename_i c l h
      have := MysteryEvents.ok_eq w e _ h
      rw [h₁] at this
      exact this.symm
    · rename_i r l h
      have hm := (MysteryEvents.ok_eq w e _ h).symm.trans h₁
      simp only [mysOk, Bool.and_eq_true] at hm
      simp only [Bool.and_eq_true]
      exact ⟨hm.2, hm.1⟩
    · rfl

end

end LangLib.World
