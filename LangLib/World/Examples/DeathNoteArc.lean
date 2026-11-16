import Lean.Data.Json
import LangLib.World.Derive
import LangLib.World.DeathNote
import LangLib.World.Mystery

/-!
# Example: Light against L (space + minds + the Death Note + fair play)

The opening of the Kira investigation in *Death Note*, from the first
killings to the To-Oh entrance ceremony where L tells Light who he is, read
move by move into the Death Note module. The prose is ours
(`stories/death-note/`, 36 paragraphs); `p01`..`p36` here are its paragraphs,
and each paragraph's `events.json` lists these moves under `"deathnote"`.

The arc is a battle of knowledge on both sides. Light kills with a face and a
real name, and has no way to tell a real name from an alias except by writing
it and waiting forty seconds. L reasons from what each death shows (the region
of a broadcast, the hours of the killings, what only the police knew) to who
Kira must be, and every one of his conclusions is a `conclude` move of the
Mystery module: allowed only if it follows from evidence he holds at that
point. The reader is a character too (`reader`): what the page has shown them,
and every conclusion the text confirms must follow from it.

The cast: Light, L, Ryuk, Raye Penber, Naomi Misora, Soichiro Yagami, the
convict shown as "Lind L. Tailor", Kiichiro Osoreda, the FBI agents (one group),
the idol Hideki Ryuga (whose name L borrows), four groups of criminals, the
people on the bus, and the reader.
-/

namespace LangLib.World.DeathNoteArc
open LangLib.World

inductive Ch | light | l | ryuk | raye | naomi | soichiro | tailor | osoreda | agents | ryuga
  | crimsA | crimsB | prisoners | crimsC | crowd | reader
  deriving DecidableEq, Repr

inductive Pl | lightRoom | npa | lRoom | studio | street | bus | train | station | npaFront | tooh
  | prison | elsewhere | page
  deriving DecidableEq, Repr

/-- Names as written. `lReal` is L's real name: nobody in the arc learns it. -/
inductive Nm | lightN | lReal | lAlias | ryuzaki | ryugaN | tailorN | rayeN | naomiN | maki
  | soichiroN | osoredaN | agentsN | crimsAN | crimsBN | prisonersN | crimsCN | ryukN | crowdN | readerN
  deriving DecidableEq, Repr

inductive Ks | heartAttack | runOver | vanish | trainCrash | oldAge
  deriving DecidableEq, Repr

inductive Ac | writeLetter | hijack | flee | crashBus | getFiles | writeNames | walkAway | drawL
  deriving DecidableEq, Repr

open Ch Pl Nm Ks Ac

def realName : Ch → Nm
  | light => lightN | l => lReal | ryuk => ryukN | raye => rayeN | naomi => naomiN
  | soichiro => soichiroN | tailor => tailorN | osoreda => osoredaN | agents => agentsN
  | ryuga => ryugaN | crimsA => crimsAN | crimsB => crimsBN | prisoners => prisonersN
  | crimsC => crimsCN | crowd => crowdN | reader => readerN

def label : Ch → String
  | light => "Light" | l => "L" | ryuk => "Ryuk" | raye => "Raye Penber" | naomi => "Naomi Misora"
  | soichiro => "Soichiro Yagami" | tailor => "the man on air" | osoreda => "Kiichiro Osoreda"
  | agents => "the FBI agents" | ryuga => "the idol Hideki Ryuga" | crimsA => "the first criminals"
  | crimsB => "the criminals of the timing pattern" | prisoners => "the prisoners"
  | crimsC => "the criminals on the evening news" | crowd => "the people on the bus" | reader => "the reader"

def spell : Nm → String
  | lightN => "Light Yagami" | lReal => "(L's real name)" | lAlias => "L" | ryuzaki => "Ryuzaki"
  | ryugaN => "Hideki Ryuga" | tailorN => "Lind L. Tailor" | rayeN => "Raye Penber"
  | naomiN => "Naomi Misora" | maki => "Shoko Maki" | soichiroN => "Soichiro Yagami"
  | osoredaN => "Kiichiro Osoreda" | agentsN => "the agents' names" | crimsAN => "the first names"
  | crimsBN => "the pattern's names" | prisonersN => "the prisoners' names" | crimsCN => "the news names"
  | ryukN => "Ryuk" | crowdN => "the passengers' names" | readerN => "the reader"

def causes : Ks → CauseDef Ch
  | heartAttack => { name := "a heart attack" }
  | runOver => { name := "being run over" }
  | vanish => { name := "a death where the body is never found" }
  | trainCrash => { name := "a train crash", harms := [crowd] }
  | oldAge => { name := "old age", possible := fun _ => false }

def acts : Ac → ActDef Ch
  | writeLetter => { name := "write a letter with a hidden message", able := (· == prisoners) }
  | hijack => { name := "take the bus at gunpoint", able := (· == osoreda) }
  | flee => { name := "run off the bus into the road", able := (· == osoreda) }
  | crashBus => { name := "drive the bus off the road", harms := [crowd, raye, light] }
  | getFiles => { name := "get the file of the FBI agents in Japan", able := (· == raye) }
  | writeNames => { name := "write the agents' names on the pages", able := (· == raye) }
  | walkAway => { name := "go somewhere she will never be found" }
  | drawL => { name := "draw L's face", able := fun _ => false }

/-! ## The minds' facts -/

/-- What the investigation turns on. -/
inductive Ck
  | kira (c : Ch) | isL (c : Ch)
  /-- the Tailor broadcast went out in the Kanto region only -/
  | kantoOnly | kiraInKanto
  /-- only criminals whose faces were shown have died -/
  | onlyShownFaces | needsFace
  /-- criminals reported under a wrong name, or none, have lived -/
  | misnamedLive | needsName
  /-- the deaths fall in a student's free hours -/
  | schoolHours | kiraStudent
  /-- L told the student theory to the task force and nobody else -/
  | toldOnlyPolice | patternChanged | policeLeak
  /-- prisoners did what they could not have meant to before they died -/
  | prisonersActed | controlsActions
  /-- Raye's assignments included the Yagami household -/
  | rayeTailedYagami | agentsAllDied | nearTailedFamily
  /-- nothing but Light could fit (never established) -/
  | noOtherSuspect
  | cleanOnCamera | watched
  | pagesOrdinary | rayeWillLive | lightHelpsL
  | hijackerSawSomething | rayeShowedId | kiraOnBus
  | makiNoDeath | lSpokeAfter | ryugaIsIdol | lRevealed | lDeathPointsToLight
  deriving DecidableEq, Repr

inductive Fact | space (x : SpaceFact Ch Pl Unit) | note (x : NoteFact Ch Nm) | ck (x : Ck)
  deriving DecidableEq, Repr, StoryFact

def Ck.truth : Ck → Bool
  | .kira c => c == light | .isL c => c == l
  | .noOtherSuspect | .pagesOrdinary | .rayeWillLive | .lightHelpsL => false
  | _ => true

structure W where
  loc : Ch → Pl
  beliefs : Ch → List (Held Ch Fact)
  note : NoteState Ch Nm Ks Ac
  mys : MysState Ch Fact := {}
  now : Nat := 0

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

instance : HasSpace W Ch Pl Unit where
  loc := W.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder _ _ := none
  setHolder w _ _ := w
  objLoc _ _ := .elsewhere
  setObjLoc w _ _ := w

instance : HasMinds W Ch Fact where
  beliefs := W.beliefs
  setBeliefs w c bs := { w with beliefs := upd w.beliefs c bs }

instance : HasNote W Ch Nm Ks Ac := ⟨W.note, fun w s => { w with note := s }⟩
instance : HasMystery W Ch Fact := ⟨W.mys, fun w s => { w with mys := s }⟩
instance : Clock W := ⟨W.now, fun w => { w with now := w.now + 1 }⟩
instance : Truth W Ck := ⟨fun _ x => x.truth⟩

instance : Cast Ch := ⟨[light, l, ryuk, raye, naomi, soichiro, tailor, osoreda, agents, ryuga,
  crimsA, crimsB, prisoners, crimsC, crowd, reader]⟩

/-- The minds the arc follows: the living among Light, L, Raye, Naomi and Soichiro
(the reader learns only what the page shows: `clue reader ...`). -/
instance (priority := high) : Perceives W Ch where
  perceives w c := w.note.alive c && [light, l, raye, naomi, soichiro].contains c

inductive E | space (x : SpaceEv Ch Pl Unit) | mind (x : MindEv Ch Fact)
  | dn (x : NoteEv Ch Nm Ks Ac Pl) | mys (x : MysEv Ch Fact)
  deriving DecidableEq, Repr, StoryEvent

def ck (x : Ck) : Fact := ev x
def nf (x : NoteFact Ch Nm) : Fact := ev x
def sp (e : SpaceEv Ch Pl Unit) : E := ev e
def mi (e : MindEv Ch Fact) : E := ev e
def dn (e : NoteEv Ch Nm Ks Ac Pl) : E := ev e
def my (e : MysEv Ch Fact) : E := ev e

def yes (x : Ck) : BLit Fact := (ck x, true)
def no (x : Ck) : BLit Fact := (ck x, false)

/-! ## The rules of deduction (L's, Naomi's, Light's, and the reader's) -/

instance : Deduction Fact where
  rules :=
    [ { name := "region", body := [(nf (.dead tailor), true), yes .kantoOnly], head := yes .kiraInKanto },
      { name := "face", body := [yes .onlyShownFaces], head := yes .needsFace },
      { name := "name", body := [yes .misnamedLive, yes .needsFace], head := yes .needsName },
      { name := "hours", body := [yes .schoolHours], head := yes .kiraStudent },
      { name := "leak", body := [yes .toldOnlyPolice, yes .patternChanged], head := yes .policeLeak },
      { name := "control", body := [yes .prisonersActed], head := yes .controlsActions },
      { name := "narrow", body := [yes .policeLeak, yes .rayeTailedYagami, yes .agentsAllDied], head := yes .nearTailedFamily },
      { name := "suspect", body := [yes .nearTailedFamily, yes .kiraStudent, yes .noOtherSuspect], head := yes (.kira light) },
      { name := "bus", body := [yes .hijackerSawSomething], head := yes .controlsActions },
      { name := "onBus", body := [yes .controlsActions, yes .rayeShowedId], head := yes .kiraOnBus },
      { name := "alias", body := [yes .makiNoDeath], head := (nf (.nameOf naomi maki), false) },
      { name := "notL", body := [yes .lSpokeAfter], head := no (.isL tailor) },
      { name := "idol", body := [yes .ryugaIsIdol], head := (nf (.nameOf l ryugaN), false) },
      { name := "guard", body := [yes .lRevealed], head := yes .lDeathPointsToLight } ]

/-! ## The opening -/

def kanto : List Pl := [lightRoom, npa, lRoom, studio, street, bus, train, station, npaFront, tooh, prison]

def note₀ : NoteState Ch Nm Ks Ac where
  realName := realName
  label := label
  spell := spell
  causes := causes
  actDefs := acts
  owner := some light
  holds := (· == light)
  touched := (· == light)
  life | light => 21900 | _ => 0

def start : W where
  loc | light | ryuk => lightRoom | l => lRoom | soichiro => npa | tailor => studio
      | crimsA | crimsB | prisoners | crimsC => prison | reader => page | _ => elsewhere
  beliefs _ := []
  note := note₀

def day : Nat := 86400

/-! ## The arc, paragraph by paragraph -/

/-- 1. Light writes the names of criminals shown on the news; Ryuk watches. -/
def p01 : List E :=
  [dn (.broadcast crimsA crimsAN kanto), dn (.write light crimsAN crimsA), dn (.seeShinigami light),
   dn (.pass 40), dn (.died crimsA), my (.clue reader (yes (.kira light)) .seen)]

/-- 2. Criminals die of heart attacks; the task force meets, and L joins it as a letter on a screen. -/
def p02 : List E :=
  [dn (.pass day), dn (.hearName soichiro l lAlias),
   mi (.notice soichiro (no (.kira light)) .assumed)]

/-- 3. L's trap: a condemned man, under his own name, to be shown in one region only. -/
def p03 : List E :=
  [dn (.dossier l tailor), my (.clue l (yes .kantoOnly) .self), my (.clue reader (yes .kantoOnly) .seen)]

/-- 4. The broadcast: "I am L". Light writes the name and pictures the face. -/
def p04 : List E :=
  [dn (.broadcast tailor tailorN kanto), mi (.notice light (yes (.isL tailor)) (.told tailor)),
   dn (.write light tailorN tailor)]

/-- 5. Forty seconds; the man dies on air. -/
def p05 : List E :=
  [dn (.pass 40), dn (.died tailor), my (.clue light (nf (.dead tailor), true) .seen),
   my (.clue reader (nf (.dead tailor), true) .seen)]

/-- 6. The real L speaks: the broadcast was Kanto only, so Kira is in Kanto. -/
def p06 : List E :=
  [dn (.hearName light l lAlias), my (.clue light (yes .lSpokeAfter) .seen),
   my (.conclude light (no (.isL tailor))),
   my (.clue l (nf (.dead tailor), true) .seen), my (.conclude l (yes .kiraInKanto)),
   my (.reveal reader (yes .kiraInKanto))]

/-- 7. L to the task force: Kira needs a face, and probably a name. -/
def p07 : List E :=
  [my (.clue l (yes .onlyShownFaces) .seen), my (.conclude l (yes .needsFace)),
   my (.clue l (yes .misnamedLive) .seen), my (.suspect l (yes .needsName) 80),
   mi (.message l soichiro (yes .needsFace)),
   my (.clue reader (yes .onlyShownFaces) .seen), my (.reveal reader (yes .needsFace))]

/-- 8. The hours of the deaths: a student's. L tells the task force, and nobody else. -/
def p08 : List E :=
  [dn (.pass (10 * day)), dn (.broadcast crimsB crimsBN kanto), dn (.write light crimsBN crimsB),
   dn (.pass 40), dn (.died crimsB),
   my (.clue l (yes .schoolHours) .seen), my (.conclude l (yes .kiraStudent)),
   mi (.message l soichiro (yes .kiraStudent)), my (.clue l (yes .toldOnlyPolice) .self),
   my (.clue reader (yes .schoolHours) .seen), my (.reveal reader (yes .kiraStudent)),
   my (.clue reader (yes .toldOnlyPolice) .seen)]

/-- 9. Light reads his father's files: the student theory, and the prisoners' records. -/
def p09 : List E :=
  [mi (.notice light (yes .kiraStudent) (.relayed soichiro)), dn (.dossier light prisoners)]

/-- 10. Light's counter-move: deaths at every hour, and prisoners who write before they die. -/
def p10 : List E :=
  [dn (.write light prisonersN prisoners), dn (.cause light prisoners heartAttack),
   dn (.details light prisoners [writeLetter] (some (3 * day)))]

/-- 11. The prisoners write their letters and die at the hours written. -/
def p11 : List E :=
  [dn (.act prisoners writeLetter), dn (.pass (3 * day)), dn (.died prisoners)]

/-- 12. L: the pattern broke the day after only the police were told, so Kira
sees police information; the prisoners show he controls what they do. -/
def p12 : List E :=
  [my (.clue l (yes .patternChanged) .seen), my (.conclude l (yes .policeLeak)),
   my (.clue l (yes .prisonersActed) .seen), my (.conclude l (yes .controlsActions)),
   my (.clue reader (yes .patternChanged) .seen), my (.clue reader (yes .prisonersActed) .seen),
   my (.reveal reader (yes .policeLeak)), my (.reveal reader (yes .controlsActions))]

/-- 13. The FBI sends agents to watch the families with access; Raye takes the Yagamis. -/
def p13 : List E :=
  [my (.clue l (yes .rayeTailedYagami) .self), my (.clue reader (yes .rayeTailedYagami) .seen),
   sp (.move raye street)]

/-- 14. Light notices the man behind him. -/
def p14 : List E :=
  [sp (.move light street), dn (.see light raye .inPerson)]

/-- 15. At home Light writes a wanted man's name, and what he will do. -/
def p15 : List E :=
  [sp (.move light lightRoom), dn (.broadcast osoreda osoredaN kanto), dn (.write light osoredaN osoreda),
   dn (.cause light osoreda runOver),
   dn (.details light osoreda [hijack, flee] (some day))]

/-- 16. The bus: Light, and the man who follows him. -/
def p16 : List E :=
  [dn (.pass (day - 600)), sp (.move light bus), sp (.move raye bus), sp (.move osoreda bus)]

/-- 17. The hijack; a scrap of the note in the gunman's hand, and he sees Ryuk. -/
def p17 : List E :=
  [dn (.act osoreda hijack), dn (.givePage light osoreda), dn (.seeShinigami osoreda),
   my (.clue reader (yes .hijackerSawSomething) .seen)]

/-- 18. Raye shows Light his badge: the real name. -/
def p18 : List E :=
  [dn (.showId raye light), my (.clue reader (yes .rayeShowedId) .seen)]

/-- 19. The gunman runs into the road and is struck. -/
def p19 : List E :=
  [dn (.act osoreda flee), sp (.move osoreda street), dn (.pass 600), dn (.died osoreda)]

/-- 20. Light writes Raye's name, and a week of what he will do. -/
def p20 : List E :=
  [sp (.move light lightRoom), dn (.write light rayeN raye), dn (.cause light raye heartAttack),
   dn (.details light raye [getFiles, writeNames] (some (7 * day)))]

/-- 21. The train: a voice behind Raye, an envelope, pages, the file, the names. -/
def p21 : List E :=
  [dn (.pass (7 * day - 600)), sp (.move light train), sp (.move raye train), dn (.givePage light raye),
   mi (.lie light raye (yes .pagesOrdinary)), mi (.lie light raye (yes .rayeWillLive)),
   dn (.act raye getFiles), dn (.dossier raye agents), dn (.act raye writeNames),
   dn (.write raye agentsN agents)]

/-- 22. The agents die; Raye steps off, turns, sees Light's face, and dies. -/
def p22 : List E :=
  [dn (.pass 40), dn (.died agents), sp (.move raye station), sp (.move light station),
   dn (.see raye light .inPerson), mi (.notice raye (yes (.kira light)) .seen),
   dn (.pass 560), dn (.died raye)]

/-- 23. L meets what is left of the task force in person, and narrows the field. -/
def p23 : List E :=
  [dn (.pass (2 * day)), sp (.move soichiro lRoom), dn (.see soichiro l .inPerson), dn (.introduce l soichiro lAlias),
   my (.clue l (yes .agentsAllDied) .seen), my (.conclude l (yes .nearTailedFamily)),
   my (.clue reader (yes .agentsAllDied) .seen), my (.reveal reader (yes .nearTailedFamily))]

/-- 24. Naomi Misora works out what Raye's death means. -/
def p24 : List E :=
  [my (.clue naomi (yes .hijackerSawSomething) (.told raye)), my (.clue naomi (yes .rayeShowedId) (.told raye)),
   my (.conclude naomi (yes .controlsActions)), my (.conclude naomi (yes .kiraOnBus)),
   my (.reveal reader (yes .kiraOnBus))]

/-- 25. The front desk of police headquarters; Light comes by. -/
def p25 : List E :=
  [dn (.pass (3 * day)), sp (.move soichiro npa), sp (.move naomi npaFront), sp (.move light npaFront),
   dn (.see light naomi .inPerson), dn (.see naomi light .inPerson)]

/-- 26. She gives a false name; he writes it. -/
def p26 : List E :=
  [dn (.introduce naomi light maki), mi (.lie light naomi (yes .lightHelpsL)),
   dn (.write light maki naomi)]

/-- 27. Forty seconds. She is still talking. -/
def p27 : List E :=
  [dn (.pass 40), dn (.lives naomi), my (.clue light (yes .makiNoDeath) .seen),
   my (.conclude light (nf (.nameOf naomi maki), false))]

/-- 28. She tells him what she knows; he tells her what headquarters will need. -/
def p28 : List E :=
  [mi (.tell naomi light (yes .controlsActions)), dn (.showId naomi light)]

/-- 29. He writes her real name, a cause, and where she will go. -/
def p29 : List E :=
  [dn (.write light naomiN naomi), dn (.cause light naomi vanish),
   dn (.details light naomi [walkAway] (some 3600))]

/-- 30. She walks away, and is not seen again. -/
def p30 : List E :=
  [dn (.act naomi walkAway), sp (.move naomi elsewhere), sp (.move light lightRoom),
   dn (.pass 3600), dn (.died naomi)]

/-- 31. L puts cameras in the Yagami house; he suspects Light, a little. -/
def p31 : List E :=
  [dn (.pass (2 * day)), my (.suspect l (yes (.kira light)) 5), mi (.message l soichiro (yes .nearTailedFamily))]

/-- 32. Light finds his door trap sprung. -/
def p32 : List E :=
  [mi (.notice light (yes .watched) .seen)]

/-- 33. A bag of crisps, a small television, a scrap of the note. -/
def p33 : List E :=
  [dn (.broadcast crimsC crimsCN kanto), dn (.write light crimsCN crimsC), dn (.pass 40), dn (.died crimsC)]

/-- 34. The cameras show nothing. L does not let go; Soichiro is relieved. -/
def p34 : List E :=
  [my (.clue l (yes .cleanOnCamera) .seen), my (.suspect l (yes (.kira light)) 5),
   my (.clue soichiro (yes .cleanOnCamera) .seen), mi (.notice soichiro (no (.kira light)) .inferred),
   my (.clue reader (yes .cleanOnCamera) .seen)]

/-- 35. The entrance exam; the young man in the seat behind. -/
def p35 : List E :=
  [dn (.pass (60 * day)), sp (.move light tooh), sp (.move l tooh), dn (.see light l .inPerson),
   dn (.see l light .inPerson)]

/-- 36. The ceremony: a name that is an idol's, and "I am L". -/
def p36 : List E :=
  [dn (.introduce l light ryugaN), dn (.introduce l light lAlias),
   my (.clue light (yes .ryugaIsIdol) .self), my (.conclude light (nf (.nameOf l ryugaN), false)),
   my (.clue light (yes .lRevealed) .seen), my (.conclude light (yes .lDeathPointsToLight)),
   dn (.lives l)]

def paras : List (List E) :=
  [p01, p02, p03, p04, p05, p06, p07, p08, p09, p10, p11, p12, p13, p14, p15, p16, p17, p18,
   p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36]

def arc : List E := paras.flatten

def after (k : Nat) : W := run start ((paras.take k).flatten)
def ends : W := run start arc

/-- The state after paragraphs `1..k` and the first `n` moves of paragraph `k + 1`. -/
def during (k n : Nat) : W := run (after k) ((paras.getD k []).take n)

/-! ## The Death Note half on its own

The note's preconditions and steps read places and the note, never minds or
the investigation; minds and the investigation never touch places or the note.
So the arc projected to its space and note moves, run in a world without minds
(`NW`), is the note half of the full run (`run_proj`), and a valid arc has a
valid note half (`valid_proj`). The counterfactuals about the note are checked
there. -/

structure NW where
  loc : Ch → Pl
  note : NoteState Ch Nm Ks Ac

instance : HasSpace NW Ch Pl Unit where
  loc := NW.loc
  setLoc w c p := { w with loc := upd w.loc c p }
  holder _ _ := none
  setHolder w _ _ := w
  objLoc _ _ := .elsewhere
  setObjLoc w _ _ := w

instance : HasNote NW Ch Nm Ks Ac := ⟨NW.note, fun w s => { w with note := s }⟩

inductive EN | space (x : SpaceEv Ch Pl Unit) | dn (x : NoteEv Ch Nm Ks Ac Pl)
  deriving DecidableEq, Repr, StoryEvent

instance (priority := high) : Perceive NW EN := Perceive.none

def abs : E → Option EN
  | .space x => some (.space x) | .dn x => some (.dn x) | .mind _ | .mys _ => none

def proj (w : W) : NW := ⟨w.loc, w.note⟩

theorem proj_foldl {β : Type} (f : W → β → W) (hf : ∀ w x, proj (f w x) = proj w) :
    ∀ (ls : List β) (w₀ : W), proj (ls.foldl f w₀) = proj w₀
  | [], _ => rfl
  | x :: ls, w₀ => by rw [List.foldl_cons, proj_foldl f hf ls, hf]

theorem proj_learnWith (k : Bool) (w : W) (c : Ch) (b : Belief Ch Fact) (e : Evid Ch) :
    proj (learnWith k w c b e) = proj w := by
  unfold learnWith
  split
  · rfl
  · simp only []
    split
    · rfl
    · rw [proj_foldl _ (fun w x => by rcases x; rfl)]; rfl

theorem proj_learn (w : W) (c : Ch) (b : Belief Ch Fact) (e : Evid Ch) :
    proj (learn w c b e) = proj w := proj_learnWith _ _ _ _ _

theorem proj_witness (w : W) (p : Pl) (φs : List Fact) : proj (witness w p φs) = proj w := by
  unfold witness
  refine proj_foldl _ (fun w x => ?_) _ _
  refine proj_foldl _ (fun w φ => ?_) _ _
  rw [proj_foldl _ (fun w y => proj_learnWith _ _ _ _ _)]; exact proj_learnWith _ _ _ _ _

theorem proj_record (b w : W) : proj (recordSettled (Φ := Fact) b w) = proj w := by
  unfold recordSettled
  split
  · rfl
  · exact proj_foldl _ (fun _ _ => rfl) _ _

theorem proj_perceive (w w' : W) (e : E) : proj (Perceive.perceive w e w') = proj w' := by
  simp only [Perceive.perceive]
  rw [proj_record]
  split
  · exact proj_witness _ _ _
  · rfl

theorem proj_step_mind (w : W) (x : MindEv Ch Fact) : proj (Domain.step w (E.mind x)) = proj w := by
  cases x with
  | tell c d lt =>
    show proj (learn (List.foldl _ (meet w c d) _) c _ _) = proj w
    rw [proj_learn, proj_foldl _ (fun w x => proj_learn _ _ _ _)]; rfl
  | whisper c d lt => show proj (learn (learn (meet w c d) d _ _) c _ _) = proj w; rw [proj_learn, proj_learn]; rfl
  | lie c d lt => show proj (learn (learn (meet w c d) d _ _) c _ _) = proj w; rw [proj_learn, proj_learn]; rfl
  | message c d lt => show proj (learn (learn w d _ _) c _ _) = proj w; rw [proj_learn, proj_learn]
  | notice c lt e => exact proj_learn _ _ _ _
  | realise c lt => exact proj_learn _ _ _ _

theorem proj_step_mys (w : W) (x : MysEv Ch Fact) : proj (Domain.step w (E.mys x)) = proj w := by
  cases x with
  | clue c lt e => exact proj_learn _ _ _ _
  | conclude c lt => exact (proj_learn _ _ _ _).trans rfl
  | suspect c lt p => rfl
  | reveal r lt => rfl

theorem proj_next (w : W) (e : E) :
    proj (next w e) = match abs e with | some e' => next (proj w) e' | none => proj w := by
  show proj (Clock.tick (Perceive.perceive w e (Domain.step w e))) = _
  rw [show ∀ v : W, proj (Clock.tick v) = proj v from fun _ => rfl, proj_perceive]
  cases e with
  | space x => cases x <;> rfl
  | mind x => exact proj_step_mind w x
  | mys x => exact proj_step_mys w x
  | dn x => cases x <;> rfl

theorem ok_abs (w : W) (e : E) (e' : EN) (h : abs e = some e') : Domain.ok w e = Domain.ok (proj w) e' := by
  cases e with
  | space x => cases h; cases x <;> rfl
  | dn x => cases h; cases x <;> rfl
  | mind x => cases h
  | mys x => cases h

/-- Running the arc and projecting is running its note half. -/
theorem run_proj : ∀ (w : W) (es : List E), proj (run w es) = run (proj w) (es.filterMap abs)
  | _, [] => rfl
  | w, e :: es => by
    have ih := run_proj (next w e) es
    rw [proj_next] at ih
    cases e <;> exact ih

/-- A valid arc has a valid note half: a move of the note that fails on its own fails the arc. -/
theorem valid_proj : ∀ (w : W) (es : List E), Valid w es → Valid (proj w) (es.filterMap abs)
  | _, [], _ => .nil
  | w, e :: es, .cons h₁ _ h₃ => by
    have ih := valid_proj _ _ h₃
    rw [proj_next] at ih
    cases e with
    | space x => exact .cons (by rw [← ok_abs w (.space x) _ rfl]; exact h₁) rfl ih
    | dn x => exact .cons (by rw [← ok_abs w (.dn x) _ rfl]; exact h₁) rfl ih
    | mind x => exact ih
    | mys x => exact ih

theorem not_valid_of_proj {w : W} {es : List E} (h : ¬ Valid (proj w) (es.filterMap abs)) :
    ¬ Valid w es := fun hv => h (valid_proj w es hv)

theorem note_run (w : W) (es : List E) : (run w es).note = (run (proj w) (es.filterMap abs)).note :=
  congrArg NW.note (run_proj w es)

/-! ## The arc is valid, move by move (minds, the note and the investigation together) -/

theorem arc_valid : Valid start arc := by decide +kernel

/-- The note half on its own. -/
theorem note_half_valid : Valid (proj start) (arc.filterMap abs) := valid_proj _ _ arc_valid

def upto (k : Nat) : List E := (paras.take k).flatten

/-! ## Who died, when, and of what -/

/-- The man on air died of a heart attack forty seconds after Light wrote the
name he was shown under; Raye of a heart attack at the hour Light set a week
before; Naomi of the cause Light wrote, an hour after the details. -/
theorem deaths :
    ends.note.deathAt tailor = some (86480, none) ∧
    ends.note.deathAt raye = some (1900920, some heartAttack) ∧
    ends.note.deathAt naomi = some (2336560, some vanish) ∧
    ends.note.alive l = true ∧ ends.note.alive light = true := by
  unfold ends; rw [note_run]; decide +kernel

/-- Naomi's alias was written, and did nothing: a fake name. -/
theorem the_alias_failed :
    (ends.note.entries.find? (·.name == maki)).map (·.void) = some (some (.fakeName maki naomi none)) := by
  unfold ends; rw [note_run]; decide +kernel

/-- Nobody but L knows L's real name; Soichiro and Light have seen his face. -/
theorem nobody_knows_ls_name :
    (Cast.all.filter fun c => ends.note.knowsName c l) = [] ∧
    ends.note.faceSeen soichiro l = true ∧ ends.note.faceSeen light l = true ∧
    ends.note.heard light l ryugaN = true ∧ ends.note.heard light l lAlias = true := by
  unfold ends; rw [note_run]; decide +kernel

/-! ## Counterfactuals: every refused write says why -/

/-- Writing "L" while picturing L's face, after the ceremony: a fake name; L lives. -/
def writeL : List E := arc ++ [dn (.write light lAlias l), dn (.pass 40), dn (.died l)]
theorem writing_L_kills_nobody : ¬ Valid start writeL := not_valid_of_proj (by decide +kernel)

/-- "Hideki Ryuga" is a real name, but the idol's: picturing L, it kills neither. -/
def writeRyuga (x : Ch) : List E := arc ++ [dn (.write light ryugaN l), dn (.pass 40), dn (.died x)]
theorem the_borrowed_name_kills_nobody :
    ¬ Valid start (writeRyuga l) ∧ ¬ Valid start (writeRyuga ryuga) :=
  ⟨not_valid_of_proj (by decide +kernel), not_valid_of_proj (by decide +kernel)⟩

/-- "Ryuzaki" is a name Light has never heard for L: he cannot even write it as L's. -/
def writeRyuzaki : List E := arc ++ [dn (.write light ryuzaki l)]
theorem ryuzaki_is_unheard : ¬ Valid start writeRyuzaki := not_valid_of_proj (by decide +kernel)

/-- Right after L's broadcast Light has a name for L ("L") and no face. -/
def noFaceYet : List E := upto 6 ++ [dn (.write light lAlias l), dn (.pass 40), dn (.died l)]
theorem no_face_no_death : ¬ Valid start noFaceYet := not_valid_of_proj (by decide +kernel)

/-- The FBI plan needs Raye's real name, which Light got from the badge: without
it, the write that the rest of the plan hangs on cannot be made. -/
def noBadge : List E := arc.filter (· != dn (.showId raye light))
theorem the_fbi_plan_needs_the_badge : ¬ Valid start noBadge := not_valid_of_proj (by decide +kernel)

/-- Naomi dies only because Light learned her real name: without her ID, he has
only the alias. -/
def noNaomiId : List E := arc.filter (· != dn (.showId naomi light))
theorem naomi_dies_by_her_real_name : ¬ Valid start noNaomiId := not_valid_of_proj (by decide +kernel)

/-- The broadcast trap needed a real name: a stand-in shown as "L" would not have
died, and there would have been no death to place Kira by. -/
def fakeStandIn : List E :=
  upto 3 ++ [dn (.broadcast tailor lAlias kanto), mi (.notice light (yes (.isL tailor)) (.told tailor)),
    dn (.write light lAlias tailor)] ++ p05
theorem the_trap_needs_a_real_name : ¬ Valid start fakeStandIn := not_valid_of_proj (by decide +kernel)

/-- Nothing Light can do to a name, short of writing it, depends on whether it
is real: what lets him write is having heard it, and whether it takes is decided
by the real name he cannot see. So the trap could not be tested before it was
sprung. -/
theorem writing_cannot_test_a_name (st : NoteState Ch Nm Ks Ac) (f : Ch → Nm) (w : NW) (c x : Ch) (n : Nm) :
    noteWhy (P := Pl) ({ w with note := { st with realName := f } }) (.write c n x) =
      noteWhy (P := Pl) ({ w with note := st }) (.write c n x) := rfl

/-- A cause impossible for the victim is refused: old age, for Naomi. -/
def oldAgeNaomi : List E :=
  upto 28 ++ [dn (.write light naomiN naomi), dn (.cause light naomi oldAge),
    dn (.details light naomi [walkAway] (some 3600))] ++ p30
theorem an_impossible_cause_is_refused : ¬ Valid start oldAgeNaomi := not_valid_of_proj (by decide +kernel)

/-- Details that would kill another are refused: the gunman driving the bus off the road. -/
def crashTheBus : List E :=
  upto 14 ++ [sp (.move light lightRoom), dn (.broadcast osoreda osoredaN kanto), dn (.write light osoredaN osoreda),
    dn (.cause light osoreda runOver), dn (.details light osoreda [hijack, crashBus] (some day))] ++ p16 ++ p17
theorem it_would_kill_another : ¬ Valid start crashTheBus := not_valid_of_proj (by decide +kernel)

def rayeWith (written : List E) : List E :=
  upto 19 ++ [sp (.move light lightRoom), dn (.write light rayeN raye)] ++ written ++ [dn (.act raye getFiles)]

/-- A train crash would kill the passengers too: refused, a heart attack at forty seconds. -/
theorem no_train_crash :
    ¬ Valid start (rayeWith [dn (.cause light raye trainCrash), dn (.details light raye [getFiles, writeNames] (some (7 * day)))]) :=
  not_valid_of_proj (by decide +kernel)

/-- The victim can only be made to do what they could do: Raye cannot draw L's face. -/
theorem raye_cannot_draw_l :
    ¬ Valid start (rayeWith [dn (.cause light raye heartAttack), dn (.details light raye [getFiles, drawL] (some (7 * day)))]) :=
  not_valid_of_proj (by decide +kernel)

/-- The windows: details later than 6 minutes 40 seconds after the cause, or a
cause later than 40 seconds after the name, are refused. -/
theorem the_windows :
    ¬ Valid start (rayeWith [dn (.cause light raye heartAttack), dn (.pass 401),
        dn (.details light raye [getFiles, writeNames] (some (7 * day)))]) ∧
    ¬ Valid start (rayeWith [dn (.pass 41), dn (.cause light raye heartAttack),
        dn (.details light raye [getFiles, writeNames] (some (7 * day)))]) :=
  ⟨not_valid_of_proj (by decide +kernel), not_valid_of_proj (by decide +kernel)⟩

/-- Only those who have touched the note see Ryuk: the gunman, after the scrap;
never Soichiro. -/
theorem who_sees_ryuk : ¬ Valid start (arc ++ [dn (.seeShinigami soichiro)]) :=
  not_valid_of_proj (by decide +kernel)

/-- The eye deal, modelled and unused: had Light made it, seeing L at the
ceremony would have shown him L's real name, and L would die; at the price of
half Light's remaining life. Only the owner can make it. -/
def withEyes : List E := dn (.eyeDeal light) :: arc ++ [dn (.write light lReal l), dn (.pass 40), dn (.died l)]
theorem the_eyes_would_end_it :
    Valid (proj start) (withEyes.filterMap abs) ∧
    (run (proj start) (withEyes.filterMap abs)).note.life light = 10950 ∧
    ¬ Valid start (arc ++ [dn (.eyeDeal soichiro)]) :=
  ⟨by decide +kernel, by decide +kernel, not_valid_of_proj (by decide +kernel)⟩

end LangLib.World.DeathNoteArc
