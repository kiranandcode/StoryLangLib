import LangLib.World.Examples.FightSnaps

/-!
# Chrollo against Hisoka: the whole fight, and who believes what

The fight is valid move by move, minds included: it is checked in four
segments (paragraphs 1-3, 4-6, 7, 8-9), each from the checkpoint the one
before it ends at (`valid_append`, `FightSnaps.lean`). The theorems about
beliefs start from the nearest checkpoint the same way.
-/

namespace LangLib.World.Fight
open LangLib.World Ch Pl Ab

theorem fight_valid : Valid start fight := by
  rw [show fight = p1 ++ p2 ++ p3 ++ (p4 ++ p5 ++ p6 ++ (p7 ++ (p8 ++ p9))) by decide +kernel,
    valid_append start (p1 ++ p2 ++ p3), at3, valid_append s3.toW (p4 ++ p5 ++ p6), at6,
    valid_append s6.toW p7, at7]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Chrollo told the truth ("it uses both hands"), and never lied... -/
theorem chrollo_told_the_truth : knows (after 3) chrollo (nf (.usesBothHands sunMoon)) = true ∧
    fight.all (fun | .mind (.lie ..) => false | _ => true) = true := by
  rw [after3]; decide +kernel

/-- ...but Hisoka took it to mean that Sun and Moon needs both hands free. -/
theorem hisoka_misreads_both_hands :
    falseBelief (after 3) hisoka (nf (.needsBothHands sunMoon)) = true := by
  rw [after3]; decide +kernel

theorem chrollo_saw_the_gum : knows (after 6) chrollo (nf (.marked c2 .gum)) = true := by
  rw [after6]; decide +kernel

/-- When the bookmark leaves Gallery Fake, the copies stay standing (the elder's
seals hold them), so Hisoka still thinks Gallery Fake is up. It is not. -/
theorem copies_outlive_gallery_fake :
    (during 6 2).nen.present c1 = true ∧
    falseBelief (during 6 2) hisoka (nf (.active chrollo galleryFake)) = true := by
  unfold during; rw [after6]; decide +kernel

/-- The decoy: when Hisoka strikes, he believes the body in front of him is
Chrollo. It is a copy wearing his face. -/
theorem hisoka_strikes_a_decoy :
    falseBelief (after 7) hisoka (nf (.is c1 chrollo)) = true ∧
    (after 7).nen.looks c1 = chrollo := by
  rw [after7]; decide +kernel

/-- Afterwards he sees through both: the decoy, and the hands. -/
theorem hisoka_sees_through_it :
    thinksNot ends hisoka (nf (.is c1 chrollo)) = true ∧
    thinksNot ends hisoka (nf (.needsBothHands sunMoon)) = true := by
  rw [ends9]; decide +kernel

/-- Nobody without a mind learns anything: the copies, made or not, hold no
beliefs at the end, and the judge none after his death. -/
theorem puppets_see_nothing :
    [c1, c2, c3, c4].all (fun x => (HasMinds.beliefs ends x).isEmpty) = true ∧
    (HasMinds.beliefs ends judge).length = (HasMinds.beliefs (run start (p1 ++ p2.take 6)) judge).length := by
  rw [ends9]; decide +kernel

/-- The dead neither talk nor hear: once the judge is dead, Chrollo cannot
whisper to him. -/
theorem no_whispers_to_the_dead :
    ¬ Valid start (p1 ++ p2 ++ [mi (.whisper chrollo judge (nf (.usesBothHands sunMoon), true))]) := by
  decide +kernel

/-- info: some (10, "the listener cannot hear (dead, or no mind)") -/
#guard_msgs in
#eval firstFailure start (p1 ++ p2 ++ [mi (.whisper chrollo judge (nf (.usesBothHands sunMoon), true))]) 0

end LangLib.World.Fight
