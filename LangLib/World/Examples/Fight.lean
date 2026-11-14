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
it at Hisoka. Hisoka strikes "Chrollo"; it is a copy, and it explodes. -/
def p7 : List E :=
  [nn (.openBook chrollo sunMoon), nn (.bookmark chrollo sunMoon), nn (.closeBook chrollo)] ++
  ([c1, c3, c4].map fun x => nn (.use chrollo sunMoon x .right)) ++
  [nn (.openBook chrollo convertHands), nn (.bookmark chrollo convertHands), nn (.closeBook chrollo),
   nn (.use chrollo convertHands c1 .right),
   nn (.openBook chrollo blackVoice), nn (.use chrollo blackVoice c1 .left), nn (.order chrollo c1),
   sp (.move chrollo ring),
   mi (.notice hisoka (nf (.is c1 chrollo), true) .inferred),
   nn (.strike hisoka c1 3), nn (.detonate c1 c1),
   mi (.notice hisoka (nf (.is c1 chrollo), false) .inferred),
   mi (.notice hisoka (nf (.needsBothHands sunMoon), false) .inferred)]

/-- 8. The bomb in the headless body: an antenna in a moon-sealed copy, the
bookmark to Black Voice, the book open at Sun and Moon, a full sun held on the
body; the controlled copy touches it. Hisoka loses his left hand. -/
def p8 : List E :=
  [sp (.move chrollo stands), nn (.use chrollo blackVoice c3 .left), nn (.bookmark chrollo blackVoice),
   nn (.openBook chrollo sunMoon), nn (.use chrollo sunMoon c2 .left), nn (.charge chrollo c2),
   nn (.order chrollo c3), sp (.move chrollo ring), nn (.detonate c2 c3), nn (.lose hisoka .left)]

/-- 9. Hisoka retreats to the upper floor; the last stamped copy, a complete
bomb, is ordered up after him. -/
def p9 : List E :=
  [sp (.move hisoka upper), sp (.move chrollo stands), nn (.openBook chrollo orderStamp),
   nn (.use chrollo orderStamp c4 .left), nn (.charge chrollo c4), nn (.order chrollo c4),
   sp (.move c4 upper), nn (.detonate c4 c4)]

def fight : List E := p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9

theorem fight_valid : Valid start fight := by decide +kernel


/-- The state after the first `k` paragraphs. -/
def after (k : Nat) : W := run start (([p1, p2, p3, p4, p5, p6, p7, p8, p9].take k).flatten)

def ends : W := run start fight

/-- The state after paragraphs `1..k` and the first `n` moves of paragraph `k + 1`. -/
def during (k n : Nat) : W := run (after k) (([p1, p2, p3, p4, p5, p6, p7, p8, p9].getD k []).take n)

/-! ## Key turns -/

/-- The moon is made with the right hand, which holds the book: before the
bookmark moves to Sun and Moon and the book shuts, it cannot be made. -/
theorem moon_needs_the_book_shut :
    ¬ Valid start (p1 ++ (p2.take 3 ++ [nn (.use chrollo sunMoon judge .right)])) := by decide +kernel

/-- info: some (6, "the right hand holds the book") -/
#guard_msgs in
#eval firstFailure start (p1 ++ (p2.take 3 ++ [nn (.use chrollo sunMoon judge .right)])) 0

/-- Taking a face needs only the left hand, free while the right holds the
book; giving his own face (the right hand) needs the book shut. -/
theorem left_hand_while_holding_the_book :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ [nn (.openBook chrollo convertHands), sp (.move chrollo stands),
      nn (.use chrollo convertHands fan .right)]) := by decide +kernel

/-- Gallery Fake needs both hands: with the book open it cannot be used. -/
theorem gallery_fake_needs_the_bookmark :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ p4 ++ [nn (.openBook chrollo galleryFake),
      nn (.use chrollo galleryFake c1 .both)]) := by decide +kernel

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

theorem the_elders_nen_outlives_him : ¬ Valid (startWith mortal) fight := by decide +kernel

/-- info: some (5, "the owner of Sun and Moon is dead, so it has gone from the book") -/
#guard_msgs in
#eval firstFailure (startWith mortal) fight 0

/-- Without Gyo, Chrollo could not have seen the gum Hisoka hid with In. -/
theorem gyo_sees_in :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6.filter (· != nn (.tech chrollo .gyo))) := by
  decide +kernel

theorem chrollo_saw_the_gum : knows (after 6) chrollo (nf (.marked c2 .gum)) = true := by decide +kernel

/-- A puppet without its head cannot carry its seal to another: the bomb in the
headless body needs a second body Chrollo controls, here with Black Voice. -/
theorem headless_bomb_needs_a_carrier :
    ¬ Valid start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++
      p8.filter fun e => e != nn (.use chrollo blackVoice c3 .left) && e != nn (.order chrollo c3)) := by
  decide +kernel

/-- info: some (73, "neither body can move to bring the seals together (a puppet without its head, nobody controlling it)") -/
#guard_msgs in
#eval firstFailure start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++
  p8.filter fun e => e != nn (.use chrollo blackVoice c3 .left) && e != nn (.order chrollo c3)) 0

/-! ## Who knows what -/

/-- Chrollo told the truth ("it uses both hands"), and never lied... -/
theorem chrollo_told_the_truth : knows (after 3) chrollo (nf (.usesBothHands sunMoon)) = true ∧
    fight.all (fun | .mind (.lie ..) => false | _ => true) = true := by decide +kernel

/-- ...but Hisoka took it to mean that Sun and Moon needs both hands free. -/
theorem hisoka_misreads_both_hands :
    falseBelief (after 3) hisoka (nf (.needsBothHands sunMoon)) = true := by decide +kernel

/-- When the bookmark leaves Gallery Fake, the copies stay standing (the elder's
seals hold them), so Hisoka still thinks Gallery Fake is up. It is not. -/
theorem copies_outlive_gallery_fake :
    (during 6 2).nen.present c1 = true ∧
    falseBelief (during 6 2) hisoka (nf (.active chrollo galleryFake)) = true := by decide +kernel

/-- The decoy: when Hisoka strikes, he believes the body in front of him is
Chrollo. It is a copy wearing his face. -/
theorem hisoka_strikes_a_decoy :
    falseBelief (during 6 15) hisoka (nf (.is c1 chrollo)) = true ∧
    (during 6 15).nen.looks c1 = chrollo := by decide +kernel

/-- Afterwards he sees through both: the decoy, and the hands. -/
theorem hisoka_sees_through_it :
    thinksNot ends hisoka (nf (.is c1 chrollo)) = true ∧
    thinksNot ends hisoka (nf (.needsBothHands sunMoon)) = true := by decide +kernel

/-! ## Where it leaves them -/

theorem hisoka_at_the_end :
    ends.nen.hurt hisoka = 10 ∧ ends.nen.hands hisoka = [.right] ∧ ends.nen.present hisoka = true := by
  decide +kernel

/-- Bungee Gum is transmutation, Hisoka's own type: he has all of it. The
book's stolen abilities keep their owners' mastery. -/
theorem affinities :
    (nen₀ defs).power hisoka bungeeGum = 100 ∧ (nen₀ defs).power chrollo galleryFake = 100 ∧
    NenType.affinity .transmuter .manipulator = 40 ∧ NenType.affinity .transmuter .specialist = 0 := by
  decide +kernel

end LangLib.World.Fight
