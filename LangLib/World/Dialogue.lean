import LangLib.World.Mind
import LangLib.World.Social

/-!
# Dialogue: questions, answers, hints, sarcasm, promises, requests

Speech acts beyond plain telling (`MindEv.tell`), after the dialogue-game
literature (questions under discussion, commitments):

* `ask c d φ`: opens a question under discussion (QUD) for `d`;
* `answer d c l`: `d` answers `c`'s open question about `l.1` honestly (they
  must think `l`); `c` learns it as testimony; the question closes;
* `hint c d l`: an implicature; `d` infers `l` as a second-hand report from `c`
  (weaker than being told outright);
* `sarcasm c d l`: `c` says the opposite of `l`, meaning `l`. A hearer with
  rapport (`Rapport`: trust or affection) gets `l`; anyone else takes the
  literal words, `~l`. Everyone else present hears the literal words too;
* `promise c d l`: `c` commits to making `l` true (a goal for `c`; see `Goals`);
* `request c d l`: `c` asks `d` to make `l` true; `d` learns `c` wants it.

All need the two together (unknown ⇒ assumed, like every other module).
-/

namespace LangLib.World

class HasDialogue (W : Type) (C Φ : outParam Type) where
  /-- open questions: (asker, asked, about) -/
  questions : W → List (C × C × Φ)
  setQuestions : W → List (C × C × Φ) → W
  /-- commitments: (speaker, to whom, what they will make true) -/
  promises : W → List (C × C × BLit Φ)
  setPromises : W → List (C × C × BLit Φ) → W
  /-- requests: (asker, asked, what they want made true) -/
  requests : W → List (C × C × BLit Φ)
  setRequests : W → List (C × C × BLit Φ) → W

/-- Does `hearer` read `speaker`'s irony? -/
class Rapport (W C : Type) where
  getsIt : W → C → C → Bool

instance (priority := low) {W C : Type} : Rapport W C := ⟨fun _ _ _ => false⟩

/-- With bonds: trust or affection of at least 2 means you read their tone. -/
def bondRapport {W C : Type} [HasBonds W C] : Rapport W C :=
  ⟨fun w h s => HasBonds.bond w h s .trust ≥ 2 || HasBonds.bond w h s .affection ≥ 2⟩

inductive DialogueEv (C Φ : Type) where
  | ask (c d : C) (φ : Φ)
  | answer (d c : C) (l : Φ × Bool)
  | hint (c d : C) (l : Φ × Bool)
  | sarcasm (c d : C) (l : Φ × Bool)
  | promise (c d : C) (l : Φ × Bool)
  | request (c d : C) (l : Φ × Bool)
  deriving DecidableEq, Repr

variable {W C P Φ : Type} [DecidableEq C] [DecidableEq P] [DecidableEq Φ]
  [HasLoc W C P] [HasMinds W C Φ] [Supersedes Φ] [Truth W Φ] [Lore Φ] [Credence W C Φ]
  [Fluent Φ] [Clock W] [PartialLoc W C] [HasDialogue W C Φ] [Rapport W C] [Cast C]

open HasLoc HasDialogue

private def flip (l : BLit Φ) : BLit Φ := (l.1, !l.2)

def isOpen (w : W) (asker asked : C) (φ : Φ) : Bool := (questions w).contains (asker, asked, φ)

def dialogueOk3 (w : W) : DialogueEv C Φ → Tri
  | .ask c d _ | .promise c d _ | .request c d _ => together3 w c d
  | .answer d c l => (together3 w c d).and (Tri.ofBool (isOpen w c d l.1 && (view w d).contains l))
  | .hint c d l | .sarcasm c d l => (together3 w c d).and (Tri.ofBool ((view w c).contains l))

/-- Everyone with `c` other than `d` hears `c`'s literal words. -/
private def overhear (w : W) (c d : C) (l : BLit Φ) : W :=
  (Cast.all.filter fun x => x != c && x != d && loc w x == loc w c).foldl
    (fun w x => learn w x (ofLit l) (.told c)) w

instance : Domain W (DialogueEv C Φ) where
  ok3 := dialogueOk3
  ok w e := dialogueOk3 w e == .yes
  step w0 e := match e with
    | .ask c d φ => setQuestions (meet w0 c d) ((c, d, φ) :: questions w0)
    | .answer d c l =>
      let w := meet w0 c d
      let w := setQuestions w ((questions w).filter (· != (c, d, l.1)))
      overhear (learn w c (ofLit l) (.told d)) d c l
    | .hint c d l => learn (meet w0 c d) d (ofLit l) (.relayed c)
    | .sarcasm c d l =>
      let w := meet w0 c d
      let heard := if Rapport.getsIt w d c then l else flip l
      overhear (learn w d (ofLit heard) (.told c)) c d (flip l)
    | .promise c d l => setPromises (meet w0 c d) ((c, d, l) :: promises w0)
    | .request c d l => setRequests (meet w0 c d) ((c, d, l) :: requests w0)
  why w
    | .answer d c l =>
      if together3 w c d == .unknown then "assumes they were together"
      else if !isOpen w c d l.1 then "nobody asked" else "the answer is not what they think"
    | .hint c d _ | .sarcasm c d _ =>
      if together3 w c d == .unknown then "assumes they were together" else "the speaker does not think that"
    | _ => "assumes they were together"

/-- Promises whose content holds in `w`, and those that do not. -/
def kept (w : W) : List (C × C × BLit Φ) := (promises w).filter fun (_, _, l) => truthLit w l
def broken (w : W) : List (C × C × BLit Φ) := (promises w).filter fun (_, _, l) => !truthLit w l

end LangLib.World
