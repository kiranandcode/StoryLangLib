import LangLib.World.Dialogue

/-!
# Goals and plans

Characters want things and act on plans (after IPOCL / Sabre's *explained
actions*: an action should serve a goal of the one who does it).

* Goals are literals a character wants true (`adopt`, `drop`); a `promise`
  counts as a goal of whoever made it.
* A plan is a goal and the steps the character intends (`intend`); `abandon`
  drops it.
* `Purpose` says, for each module's events, who acts and which facts the event
  brings about.

`motives w es` runs the story and explains every intentional action: it is the
next step of one of its agent's plans, or it brings about one of their goals.
Anything else is reported as unmotivated: not invalid (people do pointless
things), but the kind of thing a writer should either justify or cut.
`planWorks w p` checks a plan would achieve its goal from `w`.
-/

namespace LangLib.World

structure Plan (E Φ : Type) where
  goal : Φ × Bool
  steps : List E
  deriving DecidableEq, Repr

class HasGoals (W : Type) (C Φ E : outParam Type) where
  goals : W → C → List (Φ × Bool)
  setGoals : W → C → List (Φ × Bool) → W
  plans : W → C → List (Plan E Φ)
  setPlans : W → C → List (Plan E Φ) → W

inductive GoalEv (C Φ E : Type) where
  | adopt (c : C) (g : Φ × Bool)
  | drop (c : C) (g : Φ × Bool)
  | intend (c : C) (p : Plan E Φ)
  | abandon (c : C) (g : Φ × Bool)
  deriving DecidableEq, Repr

/-- Who does an event, and what it brings about. -/
class Purpose (W E C Φ : Type) where
  agent : E → Option C
  effects : W → E → List (Φ × Bool)

instance (priority := low) {W E C Φ : Type} : Purpose W E C Φ := ⟨fun _ => none, fun _ _ => []⟩

instance {W E₁ E₂ C Φ : Type} [Purpose W E₁ C Φ] [Purpose W E₂ C Φ] : Purpose W (E₁ ⊕ E₂) C Φ where
  agent | .inl e => Purpose.agent (W := W) (Φ := Φ) e | .inr e => Purpose.agent (W := W) (Φ := Φ) e
  effects w | .inl e => Purpose.effects (C := C) w e | .inr e => Purpose.effects (C := C) w e

section
variable {W C P O Φ : Type} [HasSpace W C P O] [Inject (SpaceFact C P O) Φ]

instance : Purpose W (SpaceEv C P O) C Φ where
  agent | .move c _ | .take c _ | .drop c _ | .give c _ _ => some c
  effects w
    | .move c p => [(ev (SpaceFact.at_ c p : SpaceFact C P O), true)]
    | .take c o => [(ev (SpaceFact.holds c o : SpaceFact C P O), true)]
    | .drop c o => [(ev (SpaceFact.objAt o (HasLoc.loc w c) : SpaceFact C P O), true)]
    | .give _ d o => [(ev (SpaceFact.holds d o : SpaceFact C P O), true)]
end

instance {W C Φ : Type} [Inject (SocialFact C) Φ] : Purpose W (SocialEv C) C Φ where
  agent | .flirt a _ | .confide a _ | .argue a _ | .ask a _ _ | .agree a _ _ | .withdraw a _ _ | .act a _ _ => some a
  effects _
    | .act a b x => [(ev (SocialFact.did a b x), true)]
    | _ => []

variable {W C Φ E : Type} [DecidableEq C] [DecidableEq Φ] [DecidableEq E] [HasGoals W C Φ E]
open HasGoals

instance : Domain W (GoalEv C Φ E) where
  ok _ _ := true
  step w
    | .adopt c g => setGoals w c (g :: (goals w c).filter (· != g))
    | .drop c g => setGoals w c ((goals w c).filter (· != g))
    | .intend c p => setPlans w c (p :: plans w c)
    | .abandon c g => setPlans w c ((plans w c).filter (·.goal != g))

section
variable {P : Type} [HasDialogue W C Φ]

/-- Goals of `c`: adopted ones and promises they made. -/
def goalsOf (w : W) (c : C) : List (Φ × Bool) :=
  goals w c ++ (HasDialogue.promises w).filterMap fun (s, _, l) => if s == c then some l else none

variable {S : Type} [Domain W S] [Perceive W S] [Invariant W] [Clock W] [Purpose W S C Φ]
  [Inject (GoalEv C Φ E) S] [Inject E S] [DecidableEq S]

inductive Motive (C Φ : Type) where
  | step (c : C) (g : Φ × Bool)
  | goal (c : C) (g : Φ × Bool)
  | none (c : C)
  deriving DecidableEq, Repr

/-- Walk the story; for every intentional event, why its agent did it.
Plans are tracked here: a plan step done in order advances its plan. -/
def motives : W → List S → Nat → List (Nat × Motive C Φ)
  | _, [], _ => []
  | w, e :: es, i =>
    let w' := next w e
    match Purpose.agent (W := W) (C := C) (Φ := Φ) e with
    | none => motives w' es (i + 1)
    | some c =>
      let byPlan := (plans w c).find? fun p => p.steps.head?.map (fun s => (ev s : S) == e) == some true
      let w' := match byPlan with
        | some p => setPlans w' c ((plans w' c).map fun q => if q == p then { q with steps := q.steps.tail } else q)
        | none => w'
      let m := match byPlan with
        | some p => Motive.step c p.goal
        | none =>
          match (Purpose.effects (C := C) w e).find? (goalsOf w c).contains with
          | some g => .goal c g
          | none => .none c
      (i, m) :: motives w' es (i + 1)

def unmotivated (w : W) (es : List S) : List Nat :=
  (motives w es 0).filterMap fun (i, m) => match m with | .none _ => some i | _ => none

/-- Carried out from `w`, the plan's steps are plausible and achieve its goal. -/
def planWorks [Truth W Φ] (w : W) (p : Plan E Φ) : Bool :=
  let steps : List S := p.steps.map (ev ·)
  plausibleB w steps && Truth.truth (run w steps) p.goal.1 == p.goal.2
end

end LangLib.World
