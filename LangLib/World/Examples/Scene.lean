import LangLib.World.Consent
import LangLib.World.Relationship

/-!
# A negotiated scene (invented example for `Consent` and `Relationship`)

Two friends, Ash and Bel. Bel offers to submit ("do whatever you want");
Ash takes the offer but won't act on it until Bel names what she wants. They
kiss, he asks before undressing her, checks in before sex, she asks for it
harder, and he closes the scene with aftercare. Midway he pulls her hair,
which nobody named. Afterwards he says she's his; she hasn't answered.

The theorems: the scene is plausible but rests on exactly one assumption (the
hair pull, an edge act); the blanket offer alone wouldn't have covered sex;
a withdrawal or a safeword binds until she says yes again; wanting is not agreeing; the
firsts come from history; they end as friends and lovers, not partners.
-/

namespace LangLib.World.Examples.Scene
open LangLib.World

inductive P | ash | bel
  deriving DecidableEq, Repr

open P

structure SW where
  c : ConsentState P
  r : RelState P
  deriving DecidableEq, Repr

instance : HasConsent SW P := ⟨SW.c, fun w s => { w with c := s }⟩
instance : HasRel SW P := ⟨SW.r, fun w s => { w with r := s }⟩

inductive SE | c (x : ConsentEv P) | r (x : RelEv P)
  deriving DecidableEq, Repr

instance : Domain SW SE where
  ok w | .c x => Domain.ok w x | .r x => Domain.ok w x
  ok3 w | .c x => Domain.ok3 w x | .r x => Domain.ok3 w x
  step w | .c x => Domain.step w x | .r x => Domain.step w x
  why w | .c x => Domain.why w x | .r x => Domain.why w x

instance : Perceive SW SE := Perceive.none

def start : SW :=
  { c := { never := [(bel, .penetrate)] }, r := { holds := [(ash, bel, .friends)] } }

def grant (b a : P) (x : Intim) (s : Signal) (once := false) : SE := .c (.grant b a x s once)
def act (a b : P) (x : Intim) : SE := .c (.act a b x)

def before : List SE :=
  [ .c (.wish bel ash .penetrate),                -- she wants him; she hasn't said so
    .c (.ask ash bel .kiss), grant bel ash .kiss .verbal, act ash bel .kiss,
    .c (.ask ash bel .undressTop), grant bel ash .undressTop .nod, act ash bel .undressTop,
    grant bel ash .penetrate .blanket, .c (.offer bel ash),   -- "whatever you want"
    .c (.take ash bel [.choke]),                    -- he takes it; her one limit
    .c (.command ash bel),                          -- "tell me what you want"
    grant bel ash .penetrate .verbal,
    act ash bel .grope ]                            -- inside the scene: his to lead

/-- He checks in; she says yes again. -/
def checkIn : List SE := [.c (.checkIn ash bel .penetrate), grant bel ash .penetrate .verbal]

def rest : List SE :=
  [ act ash bel .penetrate, .r (.consummate ash bel),
    act ash bel .hairPull,                          -- nobody named it
    grant bel ash .rough .verbal, act ash bel .rough,
    .r (.propose ash bel .partners),
    .c (.close ash bel true) ]

def scene : List SE := before ++ checkIn ++ rest

theorem scene_plausible : start ⊨? scene := by decide +kernel

theorem scene_assumes :
    assumptions start scene 0 =
      [(17, "hairPull is an edge act nobody named; assumes the scene's unspoken scope covers it")] := by
  decide +kernel

/-- With only the blanket offer (no named yes, no check-in), sex rests on an
assumption: taking the role sets the blanket offer aside, and the scene alone
doesn't cover sex. -/
theorem blanket_not_enough :
    (assumptions start ((before.filter (· != grant bel ash .penetrate .verbal)) ++
      [act ash bel .penetrate]) 0).map (·.2) =
      ["penetrate is a sex act nobody named; the scene alone doesn't cover it"] := by
  decide +kernel

/-- Her limit binds even inside the scene. -/
theorem limit_binds : ¬ (start ⊨? (before ++ [act ash bel .choke])) := by decide +kernel

/-- Taking it back after the check-in rules out what follows. -/
theorem withdrawal_binds :
    ¬ (start ⊨? (before ++ checkIn ++ [.c (.withdraw bel ash .penetrate)] ++ rest)) := by decide +kernel

theorem safeword_binds : ¬ (start ⊨? (before ++ checkIn ++ [.c (.stop bel ash)] ++ rest)) := by decide +kernel

/-- A withdrawal answered by a fresh yes is fine: consent is ongoing, both ways. -/
theorem withdraw_then_yes :
    start ⊨? (before ++ [.c (.withdraw bel ash .penetrate)] ++ checkIn ++ rest) := by decide +kernel

/-- A role can't be imposed: without her offer, his taking it is ruled out. -/
theorem roles_agreed : ¬ (start ⊨? scene.filter (· != .c (.offer bel ash))) := by decide +kernel

/-- Her wish is not consent: without the named yes it is still an assumption. -/
theorem wish_not_consent :
    (assumptions start [.c (.wish bel ash .penetrate), act ash bel .penetrate] 0).map (·.2) =
      ["assumes unspoken consent to penetrate (nothing asked or offered)"] := by
  decide +kernel

theorem firsts_from_history :
    (firsts start.c (scene.filterMap fun | .c x => some x | _ => none) 0).map (·.2) =
      [(bel, .penetrate)] := by
  decide +kernel

theorem friends_to_lovers :
    (run start scene).r.kinds ash bel = [.friends, .lovers] ∧
    (run start scene).r.pending ash bel = [.partners] ∧
    (run start scene).c.cared = true := by
  decide +kernel

end LangLib.World.Examples.Scene
