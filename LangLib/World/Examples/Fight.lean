import Lean.Data.Json
import LangLib.World.Derive
import LangLib.World.Nen

/-!
# Example: Chrollo against Hisoka (space + minds + Nen)

The fight at Heavens Arena (*Hunter x Hunter*), as it is shown in an animated
version of the manga, read move by move into the Nen module. The story file
with the prose is `stories/hxh-chrollo-hisoka/`; this file is its Nen half.

Chrollo fights with the pages of his book. Each stolen ability works only
while the book (held in his right hand) is open at its page or its page holds
the one bookmark, so every move he makes is a bookkeeping move too: which page
is open, where the bookmark is, which hand is free. He explains his abilities
before the fight, truthfully, and wins on what Hisoka makes of the
explanation: "it uses both hands" is true of Sun and Moon (a sun with the
left, a moon with the right), but Hisoka takes it to mean both hands must be
free, which is false. The seals are the Nen of a dead man (the elder of Meteor
City), which outlives him: they stay on whatever they mark, and the copies
they mark stay when Gallery Fake is released. So when the copies are still
standing Hisoka thinks Gallery Fake is still up, and it is not.

The cast: Chrollo, Hisoka, the judge, a spectator (`fan`) and four copies of
him (`c1`..`c4`, made in the fight). Places: the ring, the stands and the
upper floor.
-/

namespace LangLib.World.Fight
open LangLib.World

inductive Ch | chrollo | hisoka | judge | fan | c1 | c2 | c3 | c4 deriving DecidableEq, Repr
inductive Pl | ring | stands | upper deriving DecidableEq, Repr
inductive Ab | skillHunter | blackVoice | sunMoon | orderStamp | galleryFake | convertHands
  | bungeeGum | textureSurprise
  deriving DecidableEq, Repr

open Ch Pl Ab

/-- The abilities, with the conditions the fight states for them. The Nen type
of the stolen ones is not given in the fight; they keep their owners' mastery
(`power`), so it does not matter here. -/
def defs : Ab → AbilityDef
  | .skillHunter =>
    { name := "Skill Hunter", type := .specialist, cost := 0, hands := .none
      vows := ["the book is held in the right hand", "one bookmark, and only in the open page"] }
  | .blackVoice =>
    { name := "Black Voice", type := .manipulator, cost := 2, effect := .antenna
      sustained := true, stolen := true, limit := 2 }
  | .sunMoon =>
    { name := "Sun and Moon", type := .conjurer, cost := 2, effect := .seal
      stolen := true, ownerAlive := false, postMortem := true }
  | .orderStamp =>
    { name := "Order Stamp", type := .manipulator, cost := 1, effect := .stamp
      sustained := true, stolen := true, target := .puppet }
  | .galleryFake =>
    { name := "Gallery Fake", type := .conjurer, cost := 2, hands := .both, effect := .copy
      sustained := true, stolen := true }
  | .convertHands =>
    { name := "Convert Hands", type := .transmuter, cost := 2, effect := .likeness
      sustained := true, stolen := true }
  | .bungeeGum => { name := "Bungee Gum", type := .transmuter, cost := 1, hands := .none, effect := .gum }
  | .textureSurprise => { name := "Texture Surprise", type := .transmuter, cost := 1, effect := .texture }

inductive Fact | space (x : SpaceFact Ch Pl Unit) | nen (x : NenFact Ch Ab)
  deriving DecidableEq, Repr, StoryFact

structure W where
  loc : Ch → Pl
  beliefs : Ch → List (Held Ch Fact)
  nen : NenState Ch Ab

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

instance : HasSpace W Ch Pl Unit where
  loc := W.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder _ _ := none
  setHolder w _ _ := w
  objLoc _ _ := .ring
  setObjLoc w _ _ := w

instance : HasMinds W Ch Fact where
  beliefs := W.beliefs
  setBeliefs w c bs := { w with beliefs := upd w.beliefs c bs }

instance : HasNen W Ch Ab := ⟨W.nen, fun w s => { w with nen := s }⟩

instance : Cast Ch := ⟨[chrollo, hisoka, judge, fan, c1, c2, c3, c4]⟩

inductive E | space (x : SpaceEv Ch Pl Unit) | mind (x : MindEv Ch Fact) | nen (x : NenEv Ch Ab)
  deriving DecidableEq, Repr, StoryEvent

def sp (e : SpaceEv Ch Pl Unit) : E := ev e
def nn (e : NenEv Ch Ab) : E := ev e
def mi (e : MindEv Ch Fact) : E := ev e
def nf (x : NenFact Ch Ab) : Fact := ev x

def isCopy : Ch → Bool | c1 | c2 | c3 | c4 => true | _ => false

def nen₀ (d : Ab → AbilityDef) : NenState Ch Ab where
  defs := d
  type | chrollo => .specialist | hisoka => .transmuter | _ => .enhancer
  owns | chrollo => [skillHunter, blackVoice, sunMoon, orderStamp, galleryFake, convertHands]
       | hisoka => [bungeeGum, textureSurprise] | _ => []
  body c := if isCopy c then .copy else .person
  orig c := if isCopy c then fan else c
  aura | chrollo => 60 | hisoka => 40 | _ => 0
  techs _ := []
  present c := !isCopy c
  looks c := if isCopy c then fan else c

/-- What Chrollo knows of his own abilities, and tells. -/
def chrolloKnows : List Fact :=
  [nf (.usesBothHands sunMoon), nf (.needsBothHands galleryFake), nf (.can chrollo convertHands),
   nf (.can chrollo orderStamp), nf (.can chrollo galleryFake)]

def startWith (d : Ab → AbilityDef) : W where
  loc | fan | c1 | c2 | c3 | c4 => stands | _ => ring
  beliefs | chrollo => chrolloKnows.map fun φ =>
              { b := .atom φ, src := .self, rank := 10, stamp := 0, up := .hard }
          | _ => []
  nen := nen₀ d

def start : W := startWith defs

/-! ## The fight, paragraph by paragraph -/

/-- 1. Black Voice: the book open at its page, an antenna in the judge. -/
def p1 : List E :=
  [nn (.openBook chrollo blackVoice), nn (.use chrollo blackVoice judge .left), nn (.order chrollo judge)]

/-- 2. Sun and Moon on the judge: the bookmark keeps Black Voice while the book
opens at Sun and Moon; the sun with the left hand; then the bookmark moves to
Sun and Moon (Black Voice ends, the antenna goes) and the book shuts, freeing
the right hand for the moon. The marks touch. "Where's the book?" -/
def p2 : List E :=
  [nn (.bookmark chrollo blackVoice), nn (.openBook chrollo sunMoon), nn (.use chrollo sunMoon judge .left),
   nn (.bookmark chrollo sunMoon), nn (.closeBook chrollo), nn (.use chrollo sunMoon judge .right),
   nn (.detonate judge judge)]

/-- 3. Chrollo explains, truthfully; Hisoka misreads "it uses both hands". -/
def p3 : List E :=
  (chrolloKnows.map fun φ => mi (.tell chrollo hisoka (φ, true))) ++
  [mi (.notice hisoka (nf (.needsBothHands sunMoon), true) .inferred)]

/-- 4. Convert Hands with the left hand (free while the right holds the book):
Chrollo takes a spectator's face, bookmarks the page, shuts the book, and is
gone into the crowd. -/
def p4 : List E :=
  [nn (.openBook chrollo convertHands), sp (.move chrollo stands), nn (.use chrollo convertHands fan .left),
   nn (.bookmark chrollo convertHands), nn (.closeBook chrollo), nn (.hide chrollo)]

/-- 5. Gallery Fake (both hands: the bookmark, the book shut), four copies;
suns on all of them; Order Stamp on two, ordered to break Hisoka. -/
def p5 : List E :=
  [nn (.openBook chrollo galleryFake), nn (.bookmark chrollo galleryFake), nn (.closeBook chrollo)] ++
  ([c1, c2, c3, c4].map fun x => nn (.use chrollo galleryFake x .both)) ++
  [nn (.openBook chrollo sunMoon)] ++
  ([c1, c2, c3, c4].map fun x => nn (.use chrollo sunMoon x .left)) ++
  [nn (.openBook chrollo orderStamp), nn (.use chrollo orderStamp c2 .left),
   nn (.use chrollo orderStamp c3 .left),
   sp (.move hisoka stands), nn (.order chrollo c2), nn (.order chrollo c3),
   mi (.notice hisoka (nf (.active chrollo galleryFake), true) .inferred)]

/-- 6. Hisoka takes a puppet's head, sticks Bungee Gum to it under In and
swings it from his foot into a blind spot; Chrollo, with Gyo, saw it set up. -/
def p6 : List E :=
  [nn (.behead hisoka c2), nn (.tech hisoka .in_), nn (.use hisoka bungeeGum c2 .left),
   nn (.tech chrollo .gyo), nn (.spot chrollo c2), nn (.strike hisoka chrollo 2), nn (.untech hisoka .in_)]

/-- 7. The decoy. Order Stamp lapses as the page turns; the bookmark leaves
Gallery Fake, and the sealed copies stay. Moons with the right hand, the book
shut; Convert Hands' right hand gives a copy Chrollo's face; Black Voice drives
it at Hisoka, who is sure it is Chrollo. -/
def p7 : List E :=
  [nn (.openBook chrollo sunMoon), nn (.bookmark chrollo sunMoon), nn (.closeBook chrollo)] ++
  ([c1, c3, c4].map fun x => nn (.use chrollo sunMoon x .right)) ++
  [nn (.openBook chrollo convertHands), nn (.bookmark chrollo convertHands), nn (.closeBook chrollo),
   nn (.use chrollo convertHands c1 .right),
   nn (.openBook chrollo blackVoice), nn (.use chrollo blackVoice c1 .left), nn (.order chrollo c1),
   sp (.move chrollo ring),
   mi (.notice hisoka (nf (.is c1 chrollo), true) .inferred)]

/-- 8. Hisoka strikes "Chrollo": a copy, and it explodes; he sees through the
decoy and the hands. Then the bomb in the headless body: an antenna in a
moon-sealed copy, the bookmark to Black Voice, the book open at Sun and Moon,
a full sun held on the body; the controlled copy touches it. Hisoka loses his
left hand. -/
def p8 : List E :=
  [nn (.strike hisoka c1 3), nn (.detonate c1 c1),
   mi (.notice hisoka (nf (.is c1 chrollo), false) .inferred),
   mi (.notice hisoka (nf (.needsBothHands sunMoon), false) .inferred),
   sp (.move chrollo stands), nn (.use chrollo blackVoice c3 .left), nn (.bookmark chrollo blackVoice),
   nn (.openBook chrollo sunMoon), nn (.use chrollo sunMoon c2 .left), nn (.charge chrollo c2),
   nn (.order chrollo c3), sp (.move chrollo ring), nn (.detonate c2 c3), nn (.lose hisoka .left)]

/-- 9. Hisoka retreats to the upper floor; the last stamped copy, a complete
bomb, is ordered up after him. -/
def p9 : List E :=
  [sp (.move hisoka upper), sp (.move chrollo stands), nn (.openBook chrollo orderStamp),
   nn (.use chrollo orderStamp c4 .left), nn (.charge chrollo c4), nn (.order chrollo c4),
   sp (.move c4 upper), nn (.detonate c4 c4)]

def fight : List E := p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9



/-- The state after the first `k` paragraphs. -/
def after (k : Nat) : W := run start (([p1, p2, p3, p4, p5, p6, p7, p8, p9].take k).flatten)

def ends : W := run start fight

/-- The state after paragraphs `1..k` and the first `n` moves of paragraph `k + 1`.
The paragraphs are those of `stories/hxh-chrollo-hisoka`: each one's `events.json`
lists these moves under `"nen"`. -/
def during (k n : Nat) : W := run (after k) (([p1, p2, p3, p4, p5, p6, p7, p8, p9].getD k []).take n)

/-! ## The Nen half on its own

Nen's preconditions and steps read places and the Nen state, never beliefs
(only `spot` writes them), and learning never touches places or Nen. So the
story projected to its space and Nen moves, run in a world without minds
(`NW`), is the Nen half of the full run (`run_proj`), and a valid story has a
valid Nen half (`valid_proj`). Theorems about books, hands and seals are
checked there, without the minds module's cost; nothing is assumed, the
lemmas are proved for every story over this world. -/

structure NW where
  loc : Ch → Pl
  nen : NenState Ch Ab

instance : HasSpace NW Ch Pl Unit where
  loc := NW.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder _ _ := none
  setHolder w _ _ := w
  objLoc _ _ := .ring
  setObjLoc w _ _ := w

instance : HasNen NW Ch Ab := ⟨NW.nen, fun w s => { w with nen := s }⟩
/-- No minds: what is learned goes nowhere. -/
instance : HasMinds NW Ch Fact where
  beliefs _ _ := []
  setBeliefs w _ _ := w

inductive EN | space (x : SpaceEv Ch Pl Unit) | nen (x : NenEv Ch Ab)
  deriving DecidableEq, Repr, StoryEvent

instance (priority := high) : Perceive NW EN := Perceive.none

def abs : E → Option EN
  | .space x => some (.space x) | .nen x => some (.nen x) | .mind _ => none

def proj (w : W) : NW := ⟨w.loc, w.nen⟩

theorem proj_foldl {β : Type} (f : W → β → W) (hf : ∀ w x, proj (f w x) = proj w) :
    ∀ (l : List β) (w₀ : W), proj (l.foldl f w₀) = proj w₀
  | [], _ => rfl
  | x :: l, w₀ => by rw [List.foldl_cons, proj_foldl f hf l, hf]

theorem proj_learnWith (k : Bool) (w : W) (c : Ch) (b : Belief Ch Fact) (e : Evid Ch) :
    proj (learnWith k w c b e) = proj w := by
  unfold learnWith
  split
  · rfl
  · simp only []
    split
    · rfl
    · rw [proj_foldl _ (fun w x => by rcases x; rfl)]; rfl

theorem proj_witness (w : W) (p : Pl) (φs : List Fact) : proj (witness w p φs) = proj w := by
  unfold witness
  refine proj_foldl _ (fun w x => ?_) _ _
  refine proj_foldl _ (fun w φ => ?_) _ _
  rw [proj_foldl _ (fun w y => proj_learnWith _ _ _ _ _)]; exact proj_learnWith _ _ _ _ _

theorem proj_learn (w : W) (c : Ch) (b : Belief Ch Fact) (e : Evid Ch) :
    proj (learn w c b e) = proj w := proj_learnWith _ _ _ _ _

theorem nw_foldl {β : Type} (f : NW → β → NW) (hf : ∀ w x, f w x = w) :
    ∀ (l : List β) (w₀ : NW), l.foldl f w₀ = w₀
  | [], _ => rfl
  | x :: l, w₀ => by rw [List.foldl_cons, hf, nw_foldl f hf l]

/-- Without minds, learning changes nothing. -/
theorem nw_learnWith (k : Bool) (w : NW) (c : Ch) (b : Belief Ch Fact) (e : Evid Ch) :
    learnWith k w c b e = w := by
  unfold learnWith
  split
  · rfl
  · simp only []
    split
    · rfl
    · rw [nw_foldl _ (fun w x => by rcases x; rfl)]; rfl

theorem proj_perceive (w w' : W) (e : E) : proj (Perceive.perceive w e w') = proj w' := by
  simp only [Perceive.perceive]
  split
  · exact proj_witness _ _ _
  · rfl

theorem proj_step_mind (w : W) (x : MindEv Ch Fact) : proj (Domain.step w (E.mind x)) = proj w := by
  cases x with
  | tell c d l =>
    show proj (learn (List.foldl _ (meet w c d) _) c _ _) = proj w
    rw [proj_learn, proj_foldl _ (fun w x => proj_learn _ _ _ _)]; rfl
  | whisper c d l => show proj (learn (learn (meet w c d) d _ _) c _ _) = proj w; rw [proj_learn, proj_learn]; rfl
  | lie c d l => show proj (learn (learn (meet w c d) d _ _) c _ _) = proj w; rw [proj_learn, proj_learn]; rfl
  | notice c l e => exact proj_learn _ _ _ _
  | realise c l => exact proj_learn _ _ _ _

theorem proj_next (w : W) (e : E) :
    proj (next w e) = match abs e with | some e' => next (proj w) e' | none => proj w := by
  show proj (Perceive.perceive w e (Domain.step w e)) = _
  rw [proj_perceive]
  cases e with
  | space x => cases x <;> rfl
  | mind x => exact proj_step_mind w x
  | nen x =>
    cases x with
    | spot c x =>
      change proj (nenStep w (.spot c x)) = nenStep (proj w) (.spot c x)
      have l : proj (nenStep w (.spot c x)) = proj w := by
        simp only [nenStep]
        exact proj_foldl _ (fun w m => by split <;> first | exact proj_learn _ _ _ _ | rfl) _ _
      have r : nenStep (proj w) (.spot c x) = proj w := by
        simp only [nenStep]
        exact nw_foldl _ (fun w m => by split <;> first | exact nw_learnWith _ _ _ _ _ | rfl) _ _
      rw [l, r]
    | _ => rfl

theorem ok_abs (w : W) (e : E) (e' : EN) (h : abs e = some e') : Domain.ok w e = Domain.ok (proj w) e' := by
  cases e with
  | space x => cases h; cases x <;> rfl
  | nen x => cases h; cases x <;> rfl
  | mind x => cases h

/-- Running the story and projecting is running the Nen half of it. -/
theorem run_proj : ∀ (w : W) (es : List E), proj (run w es) = run (proj w) (es.filterMap abs)
  | _, [] => rfl
  | w, e :: es => by
    have ih := run_proj (next w e) es
    rw [proj_next] at ih
    cases e with
    | space x => exact ih
    | nen x => exact ih
    | mind x => exact ih

/-- A valid story has a valid Nen half: a Nen move that fails on its own fails the story. -/
theorem valid_proj : ∀ (w : W) (es : List E), Valid w es → Valid (proj w) (es.filterMap abs)
  | _, [], _ => .nil
  | w, e :: es, .cons h₁ _ h₃ => by
    have ih := valid_proj _ _ h₃
    rw [proj_next] at ih
    cases e with
    | space x => exact .cons (by rw [← ok_abs w (.space x) _ rfl]; exact h₁) rfl ih
    | nen x => exact .cons (by rw [← ok_abs w (.nen x) _ rfl]; exact h₁) rfl ih
    | mind x => exact ih

theorem not_valid_of_proj {w : W} {es : List E} (h : ¬ Valid (proj w) (es.filterMap abs)) :
    ¬ Valid w es := fun hv => h (valid_proj w es hv)

theorem nen_run (w : W) (es : List E) : (run w es).nen = (run (proj w) (es.filterMap abs)).nen :=
  congrArg NW.nen (run_proj w es)


/-! ## Snapshots

A checkpoint is the state at a paragraph boundary written out as plain data
(`Snap`: each function as its table). `toW_snap` proves the world rebuilt
from a snapshot is the world, so a theorem about a later state can start from a
checkpoint instead of replaying the story from the start (`FightSnaps.lean`
proves each checkpoint; `FightMinds.lean` uses them). -/

def allAb : List Ab := [skillHunter, blackVoice, sunMoon, orderStamp, galleryFake, convertHands,
  bungeeGum, textureSurprise]

def look {α β : Type} [DecidableEq α] (t : List (α × β)) (d : β) (a : α) : β :=
  ((t.find? (·.1 == a)).map (·.2)).getD d

def tab {α β : Type} (xs : List α) (f : α → β) : List (α × β) := xs.map fun x => (x, f x)

/-- The world as plain data: each function as its table over the cast (or the abilities). -/
structure Snap where
  loc : List (Ch × Pl)
  beliefs : List (Ch × List (Held Ch Fact))
  defs : List (Ab × AbilityDef)
  type : List (Ch × NenType)
  owns : List (Ch × List Ab)
  body : List (Ch × Body)
  orig : List (Ch × Ch)
  aura : List (Ch × Nat)
  techs : List (Ch × List Tech)
  present : List (Ch × Bool)
  headed : List (Ch × Bool)
  hands : List (Ch × List Hand)
  hurt : List (Ch × Nat)
  book : List (Ch × Book Ab)
  active : List (Ch × Ab)
  marks : List (Ch × List (Mark Ch Ab))
  looks : List (Ch × Ch)
  hidden : List (Ch × Bool)
  deriving DecidableEq, Repr

def snap (w : W) : Snap :=
  let n := w.nen
  let cs := (Cast.all : List Ch)
  { loc := tab cs w.loc, beliefs := tab cs w.beliefs, defs := tab allAb n.defs, type := tab cs n.type,
    owns := tab cs n.owns, body := tab cs n.body, orig := tab cs n.orig, aura := tab cs n.aura,
    techs := tab cs n.techs, present := tab cs n.present, headed := tab cs n.headed,
    hands := tab cs n.hands, hurt := tab cs n.hurt, book := tab cs n.book, active := n.active,
    marks := tab cs n.marks, looks := tab cs n.looks, hidden := tab cs n.hidden }

def Snap.toW (s : Snap) : W where
  loc := look s.loc .ring
  beliefs := look s.beliefs []
  nen :=
    { defs := look s.defs (Fight.defs Ab.skillHunter), type := look s.type .enhancer, owns := look s.owns [],
      body := look s.body .person, orig := look s.orig fan, aura := look s.aura 0,
      techs := look s.techs [], present := look s.present false, headed := look s.headed false,
      hands := look s.hands [], hurt := look s.hurt 0, book := look s.book {}, active := s.active,
      marks := look s.marks [], looks := look s.looks fan, hidden := look s.hidden false }

theorem toW_snap (w : W) : (snap w).toW = w := by
  obtain ⟨loc, bel, ⟨d, ty, ow, bo, og, au, te, pr, he, ha, hu, bk, ac, ma, lo, hi⟩⟩ := w
  simp only [snap, Snap.toW]
  congr <;> funext x <;> cases x <;> rfl

/-! ## Tied to the story files

Each paragraph's `events.json` lists its Nen moves under `"nen"`, one line per
move in this file's words; the guards fail if the two drift apart. -/

def nm {α : Type} [Repr α] (a : α) : String := (((reprStr a).splitOn ".").getLast!).replace "_" ""

def Fact.show : Fact → String
  | .space (.at_ c p) => s!"at({nm c},{nm p})"
  | .space _ => "?"
  | .nen x => match x with
    | .can c a => s!"can({nm c},{nm a})" | .active c a => s!"active({nm c},{nm a})"
    | .marked x k => s!"marked({nm x},{nm k})" | .looksLike x y => s!"looksLike({nm x},{nm y})"
    | .is x y => s!"is({nm x},{nm y})" | .needsBothHands a => s!"needsBothHands({nm a})"
    | .usesBothHands a => s!"usesBothHands({nm a})" | .gone x => s!"gone({nm x})"

def litShow (l : Fact × Bool) : String := (if l.2 then "" else "!") ++ l.1.show

def E.show : E → String
  | .space (.move c p) => s!"move {nm c} {nm p}"
  | .space _ => "?"
  | .mind (.tell c d l) => s!"tell {nm c} {nm d} {litShow l}"
  | .mind (.notice c l e) => s!"notice {nm c} {litShow l} {nm e}"
  | .mind _ => "?"
  | .nen x => match x with
    | .tech c t => s!"tech {nm c} {nm t}" | .untech c t => s!"untech {nm c} {nm t}"
    | .openBook c a => s!"openBook {nm c} {nm a}" | .closeBook c => s!"closeBook {nm c}"
    | .bookmark c a => s!"bookmark {nm c} {nm a}"
    | .use c a t h => s!"use {nm c} {nm a} {nm t} {nm h}"
    | .charge c t => s!"charge {nm c} {nm t}" | .release c a => s!"release {nm c} {nm a}"
    | .order c x => s!"order {nm c} {nm x}" | .behead c x => s!"behead {nm c} {nm x}"
    | .detonate x y => s!"detonate {nm x} {nm y}" | .spot c x => s!"spot {nm c} {nm x}"
    | .strike c t n => s!"strike {nm c} {nm t} {n}" | .lose c h => s!"lose {nm c} {nm h}"
    | .hide c => s!"hide {nm c}" | .emerge c => s!"emerge {nm c}"

open Lean in
def nenOf (src : String) : List String :=
  match Json.parse src with
  | .ok j => match j.getObjVal? "nen" with
    | .ok (.arr a) => a.toList.filterMap (·.getStr?.toOption)
    | _ => []
  | .error _ => []

#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/01.events.json") == p1.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/02.events.json") == p2.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/03.events.json") == p3.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/04.events.json") == p4.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/05.events.json") == p5.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/06.events.json") == p6.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/07.events.json") == p7.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/08.events.json") == p8.map E.show
#guard nenOf (include_str "../../../stories/hxh-chrollo-hisoka/paragraphs/09.events.json") == p9.map E.show

/-! ## Key turns

Each is a Nen move that fails, so each is checked on the Nen half
(`not_valid_of_proj`). What the fighters believe is in `FightMinds.lean`. -/

/-- The moon is made with the right hand, which holds the book: before the
bookmark moves to Sun and Moon and the book shuts, it cannot be made. -/
theorem moon_needs_the_book_shut :
    ¬ Valid start (p1 ++ (p2.take 3 ++ [nn (.use chrollo sunMoon judge .right)])) :=
  not_valid_of_proj (by decide +kernel)

/-- info: some (6, "the right hand holds the book") -/
#guard_msgs in
#eval firstFailure start (p1 ++ (p2.take 3 ++ [nn (.use chrollo sunMoon judge .right)])) 0

/-- Taking a face needs only the left hand, free while the right holds the
book; giving his own face (the right hand) needs the book shut. -/
theorem left_hand_while_holding_the_book :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ [nn (.openBook chrollo convertHands), sp (.move chrollo stands),
      nn (.use chrollo convertHands fan .right)]) := not_valid_of_proj (by decide +kernel)

/-- Gallery Fake needs both hands: with the book open it cannot be used. -/
theorem gallery_fake_needs_the_bookmark :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ p4 ++ [nn (.openBook chrollo galleryFake),
      nn (.use chrollo galleryFake c1 .both)]) := not_valid_of_proj (by decide +kernel)

/-- info: some (23, "Gallery Fake needs both hands free (the right one holds the book)") -/
#guard_msgs in
#eval firstFailure start (p1 ++ p2 ++ p3 ++ p4 ++ [nn (.openBook chrollo galleryFake),
  nn (.use chrollo galleryFake c1 .both)]) 0

/-- Sun and Moon belonged to the dead elder of Meteor City. Were it not Nen
made stronger by his death, it would have gone from the book with him, and the
fight could not have happened as it did. -/
def mortal : Ab → AbilityDef
  | .sunMoon => { defs .sunMoon with postMortem := false }
  | a => defs a

theorem the_elders_nen_outlives_him : ¬ Valid (startWith mortal) fight :=
  not_valid_of_proj (by decide +kernel)

/-- info: some (5, "the owner of Sun and Moon is dead, so it has gone from the book") -/
#guard_msgs in
#eval firstFailure (startWith mortal) fight 0

/-- Without Gyo, Chrollo could not have seen the gum Hisoka hid with In. -/
theorem gyo_sees_in :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6.filter (· != nn (.tech chrollo .gyo))) :=
  not_valid_of_proj (by decide +kernel)

/-- A puppet without its head cannot carry its seal to another: the bomb in the
headless body needs a second body Chrollo controls, here with Black Voice. -/
theorem headless_bomb_needs_a_carrier :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++
      p8.filter fun e => e != nn (.use chrollo blackVoice c3 .left) && e != nn (.order chrollo c3)) :=
  not_valid_of_proj (by decide +kernel)

/-- info: some (73, "neither body can move to bring the seals together (a puppet without its head, nobody controlling it)") -/
#guard_msgs in
#eval firstFailure start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++
  p8.filter fun e => e != nn (.use chrollo blackVoice c3 .left) && e != nn (.order chrollo c3)) 0

/-! ## Where it leaves them -/

theorem hisoka_at_the_end :
    ends.nen.hurt hisoka = 10 ∧ ends.nen.hands hisoka = [.right] ∧ ends.nen.present hisoka = true := by
  unfold ends; rw [nen_run]; decide +kernel

/-- Bungee Gum is transmutation, Hisoka's own type: he has all of it. The
book's stolen abilities keep their owners' mastery. -/
theorem affinities :
    (nen₀ defs).power hisoka bungeeGum = 100 ∧ (nen₀ defs).power chrollo galleryFake = 100 ∧
    NenType.affinity .transmuter .manipulator = 40 ∧ NenType.affinity .transmuter .specialist = 0 := by
  decide +kernel

end LangLib.World.Fight
