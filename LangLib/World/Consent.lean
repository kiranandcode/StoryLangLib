import LangLib.World.Social

/-!
# Consent, refined: acts, signals, scopes, scenes, check-ins, firsts

`Social` gates five coarse acts (`holdHands kiss touch undress sex`) on a
yes/no `agree`. Real scenes say more, and a story checked only at that grain
can't tell a negotiated scene from an assumed one. This module refines it:

* **Acts** (`Intim`) are finer, and each refines one of `Social`'s acts
  (`Intim.coarse`), so a story here abstracts to a story there.
  Some are *edge* acts (restraint, gagging, a hand on the throat, biting,
  marking): by convention they're negotiated by name and never covered by
  agreement to something else.
* **Grants** say who agreed to what, with whom, and *how* (`Signal`): said
  out loud, a nod, an invitation by deed (leaving a garment for the other to
  take off, pushing back), a blanket offer ("whatever you want"), or bare
  compliance under pressure. A grant can be *once* (used up by the act) or
  ongoing. Asking for an act is the asker's own grant. A grant for one act
  can cover finer acts (`Intim.covers`): agreeing to penetration covers the
  fingering that prepares it, agreeing to rough sex covers sex.
* **Scenes** are power exchange as *agreed*, not imposed: the submissive
  offers (`offer`), the dominant takes the offer (`take`) with the
  submissive's limits. Inside a scene the dominant may lead non-edge acts
  without asking each one, and may give orders (`command`); sex acts still
  need a named grant (a blanket offer doesn't cover them), and edge acts are
  never covered by the scene alone.
* **Withdrawal** (`withdraw`) removes a grant at any time and rules the act
  (and anything that includes it) out until a fresh grant; `stop` (a
  safeword) removes every grant the speaker gave, ends the scene and rules
  everything out until they say yes again. Nothing overrides either: not a
  scene, not a role (`withdraw_rules_out`, `stop_rules_out`).
* **Check-ins** (`checkIn`) ask whether a grant still holds mid-scene; the
  answer is a fresh grant or a withdrawal. **Aftercare**: `close dom sub care` ends a
  scene, with care or without; `cared` says whether every scene that ended had it.
* **Desire** (`wish`) is interior: wanting, or fantasising about, an act is
  never consent to it, and changes no grant (`wish_grants`).
* **Firsts** are facts about history, not states: the world records what
  each character has done and what they had never done before the story
  opened (`never`), and `firsts` lists every act that was someone's first.

`ok3` is three-valued: an act is `yes` when a firm grant (spoken, nodded or
invited, still standing) or the scene covers it; `no` when it's inside a
limit, after a withdrawal or a stop; and `unknown` when it rests only on a
blanket offer, on compliance, on the scene's unspoken scope for an edge act,
or on nothing said at all. `Plausible` then lists exactly those acts, so a
story's assumptions about consent are a theorem rather than a reading.
-/

namespace LangLib.World

/-- Fine-grained intimate acts. -/
inductive Intim
  /-- incidental contact that isn't sexual (riding in a lap, a hand on a shoulder) -/
  | contact
  | caress | hold | kiss | grope | undressTop | undressBottom
  | finger | penetrate | rough | finishInside
  /-- edge acts: negotiated by name -/
  | gag | bite | mark | hairPull | choke | pinDown
  deriving DecidableEq, Repr

namespace Intim

/-- The `Social` act each refines (incidental contact refines none). -/
def coarse : Intim → Option Act
  | contact => none
  | caress | hold | grope | gag | bite | hairPull | choke | pinDown => some .touch
  | kiss | mark => some .kiss
  | undressTop | undressBottom => some .undress
  | finger | penetrate | rough | finishInside => some .sex

def edge : Intim → Bool
  | gag | bite | mark | hairPull | choke | pinDown => true
  | _ => false

def isSex (x : Intim) : Bool := x.coarse == some .sex

/-- A grant for `x` covers `y`. -/
def covers (x y : Intim) : Bool :=
  x == y || match x, y with
  | grope, caress | grope, hold | hold, caress => true
  | penetrate, finger | rough, penetrate | rough, finger => true
  | _, _ => false

def name : Intim → String
  | contact => "contact" | caress => "caress" | hold => "hold" | kiss => "kiss"
  | grope => "grope" | undressTop => "undressTop" | undressBottom => "undressBottom"
  | finger => "finger" | penetrate => "penetrate" | rough => "rough"
  | finishInside => "finishInside" | gag => "gag" | bite => "bite" | mark => "mark"
  | hairPull => "hairPull" | choke => "choke" | pinDown => "pinDown"

def all : List Intim :=
  [contact, caress, hold, kiss, grope, undressTop, undressBottom, finger, penetrate, rough,
   finishInside, gag, bite, mark, hairPull, choke, pinDown]

def ofString? (s : String) : Option Intim := all.find? (·.name == s)

end Intim

/-- How agreement was given. -/
inductive Signal
  /-- said out loud: a yes, a request, a named want -/
  | verbal
  /-- a clear nonverbal yes: a nod -/
  | nod
  /-- by deed: soliciting the act itself -/
  | invite
  /-- "whatever you want": an offer, not agreement to any act in particular -/
  | blanket
  /-- going along with what a group decided -/
  | pressured
  deriving DecidableEq, Repr

def Signal.firm : Signal → Bool
  | .verbal | .nod | .invite => true
  | _ => false

/-- `giver` agrees that `taker` may do `act` with them. -/
structure Grant (C : Type) where
  giver : C
  taker : C
  act : Intim
  sig : Signal
  once : Bool := false
  deriving DecidableEq, Repr

/-- An agreed power exchange. -/
structure Scene (C : Type) where
  dom : C
  sub : C
  limits : List Intim := []
  deriving DecidableEq, Repr

structure ConsentState (C : Type) where
  grants : List (Grant C) := []
  /-- submissions offered and not yet taken: (sub, dom) -/
  offers : List (C × C) := []
  scenes : List (Scene C) := []
  /-- scenes that ended, and whether with aftercare -/
  closed : List (Scene C × Bool) := []
  /-- what has been done: (doer, with, act) -/
  done : List (C × C × Intim) := []
  /-- what each character had never done when the story opened -/
  never : List (C × Intim) := []
  /-- interior wants: (who, with whom, what) -/
  wishes : List (C × C × Intim) := []
  /-- open check-ins: (asker, asked, act) -/
  checks : List (C × C × Intim) := []
  /-- withdrawn and not given again: (giver, taker, act) -/
  revoked : List (C × C × Intim) := []
  /-- safewords not yet answered by a fresh grant: (who stopped, whom) -/
  stopped : List (C × C) := []
  deriving DecidableEq, Repr

class HasConsent (W : Type) (C : outParam Type) where
  cs : W → ConsentState C
  setCs : W → ConsentState C → W

inductive ConsentEv (C : Type) where
  /-- `a` asks to do `x` with `b` (and so agrees to it themselves) -/
  | ask (a b : C) (x : Intim)
  /-- `b` agrees that `a` may do `x` with them -/
  | grant (b a : C) (x : Intim) (s : Signal) (once : Bool)
  | withdraw (b a : C) (x : Intim)
  /-- a safeword: every grant `b` gave `a` is gone, and their scene ends -/
  | stop (b a : C)
  /-- `sub` offers to submit to `dom` -/
  | offer (sub dom : C)
  /-- `dom` takes the offer, within the sub's limits -/
  | take (dom sub : C) (limits : List Intim)
  | command (dom sub : C)
  | checkIn (a b : C) (x : Intim)
  | act (a b : C) (x : Intim)
  /-- the scene ends; `care`: with aftercare -/
  | close (dom sub : C) (care : Bool)
  | wish (c d : C) (x : Intim)
  deriving DecidableEq, Repr

variable {W C : Type} [DecidableEq C] [HasConsent W C]
open HasConsent

def ConsentState.sceneOf (s : ConsentState C) (a b : C) : Option (Scene C) :=
  s.scenes.find? fun sc => (sc.dom == a && sc.sub == b) || (sc.dom == b && sc.sub == a)

/-- A grant from `b` to `a` covering `x`, firm or not. -/
def ConsentState.grantFor (s : ConsentState C) (b a : C) (x : Intim) (firm : Bool) : Bool :=
  s.grants.any fun g => g.giver == b && g.taker == a && g.act.covers x && (!firm || g.sig.firm)

/-- `b` withdrew, or stopped, something that touches `x`. -/
def ConsentState.refused (s : ConsentState C) (b a : C) (x : Intim) : Bool :=
  s.stopped.contains (b, a) ||
  s.revoked.any fun (g, t, r) => g == b && t == a && (r.covers x || x.covers r)

/-- Does `b` consent to `a` doing `x` with them? -/
def consents3 (s : ConsentState C) (a b : C) (x : Intim) : Tri :=
  if s.refused b a x then .no else
  match s.sceneOf a b with
  | some sc =>
    if sc.limits.any (·.covers x) || sc.limits.contains x then .no
    else if s.grantFor b a x true then .yes
    else if sc.dom == a && !x.edge && !x.isSex then .yes
    else .unknown
  | none => if s.grantFor b a x true then .yes else .unknown

def consentWhy (s : ConsentState C) (a b : C) (x : Intim) : String :=
  if s.stopped.contains (b, a) then "they stopped, and haven't said yes again since"
  else if s.refused b a x then s!"{x.name}: they took it back, and haven't said yes again since" else
  match s.sceneOf a b with
  | some sc =>
    if sc.limits.contains x then s!"{x.name} is one of the scene's limits"
    else if s.grantFor b a x false then s!"{x.name} rests only on a blanket offer or on compliance"
    else if x.edge then s!"{x.name} is an edge act nobody named; assumes the scene's unspoken scope covers it"
    else if x.isSex then s!"{x.name} is a sex act nobody named; the scene alone doesn't cover it"
    else s!"assumes unspoken consent to {x.name}"
  | none =>
    if s.grantFor b a x false then s!"{x.name} rests only on a blanket offer or on compliance"
    else s!"assumes unspoken consent to {x.name} (nothing asked or offered)"

/-- Remove the first `once` grant that covered this act. -/
def ConsentState.use (s : ConsentState C) (a b : C) (x : Intim) : ConsentState C :=
  match s.grants.find? (fun g => g.giver == b && g.taker == a && g.once && g.act.covers x) with
  | some g => { s with grants := s.grants.erase g }
  | none => s

def consentOk3 (s : ConsentState C) : ConsentEv C → Tri
  | .act a b x => if a == b then .no else consents3 s a b x
  | .take dom sub _ => Tri.ofBool (s.offers.contains (sub, dom))
  | .command dom sub => if (s.sceneOf dom sub).any (·.dom == dom) then .yes else .unknown
  | .close dom sub _ => Tri.ofBool ((s.sceneOf dom sub).any (·.dom == dom))
  | _ => .yes

def consentStep (s : ConsentState C) : ConsentEv C → ConsentState C
  | .ask a b x => { s with grants := ⟨a, b, x, .verbal, false⟩ :: s.grants }
  | .grant b a x sg o =>
    { s with grants := ⟨b, a, x, sg, o⟩ :: s.grants,
             checks := s.checks.filter (· != (a, b, x)),
             revoked := s.revoked.filter fun (g, t, r) => !(g == b && t == a && (x.covers r || r.covers x)),
             stopped := s.stopped.erase (b, a) }
  | .withdraw b a x =>
    { s with grants := s.grants.filter fun g => !(g.giver == b && g.taker == a && g.act.covers x),
             checks := s.checks.filter (· != (a, b, x)),
             revoked := (b, a, x) :: s.revoked }
  | .stop b a =>
    { s with grants := s.grants.filter fun g => !(g.giver == b && g.taker == a),
             stopped := (b, a) :: s.stopped,
             scenes := s.scenes.filter fun sc => !((sc.dom == a && sc.sub == b) || (sc.dom == b && sc.sub == a)) }
  | .offer sub dom => { s with offers := (sub, dom) :: s.offers }
  | .take dom sub lim =>
    { s with offers := s.offers.erase (sub, dom), scenes := ⟨dom, sub, lim⟩ :: s.scenes,
             grants := s.grants.filter fun g => g.sig != .blanket }
  | .command _ _ => s
  | .checkIn a b x => { s with checks := (a, b, x) :: s.checks }
  | .act a b x => { (s.use a b x) with done := (a, b, x) :: s.done }
  | .close dom sub care =>
    match s.sceneOf dom sub with
    | some sc => { s with scenes := s.scenes.erase sc, closed := (sc, care) :: s.closed }
    | none => s
  | .wish c d x => { s with wishes := (c, d, x) :: s.wishes }

def consentWhyEv (s : ConsentState C) : ConsentEv C → String
  | .act a b x => if a == b then "an act needs two people" else consentWhy s a b x
  | .take _ _ _ => "nobody offered to submit: a role can't be imposed"
  | .command _ _ => "an order outside an agreed scene; assumes it is wanted"
  | .close _ _ _ => "no scene to close"
  | _ => ""

instance : Domain W (ConsentEv C) where
  ok3 w e := consentOk3 (cs w) e
  ok w e := consentOk3 (cs w) e == .yes
  step w e := setCs w (consentStep (cs w) e)
  why w e := consentWhyEv (cs w) e

/-! ## Laws -/

/-- Wanting is never agreeing: a wish changes no grant. -/
theorem wish_grants (s : ConsentState C) (c d : C) (x : Intim) :
    (consentStep s (.wish c d x)).grants = s.grants := rfl

/-- After a withdrawal, nothing the withdrawn grant covered stands. -/
theorem withdraw_removes (s : ConsentState C) (b a : C) (x : Intim) :
    (consentStep s (.withdraw b a x)).grantFor b a x false = false := by
  simp [consentStep, ConsentState.grantFor, List.any_filter]
  intro g _ h₁ h₂ h₃; simp_all

/-- After a withdrawal the act is ruled out, scene or no scene, until a fresh grant. -/
theorem withdraw_rules_out (s : ConsentState C) (b a : C) (x : Intim) :
    consents3 (consentStep s (.withdraw b a x)) a b x = .no := by
  simp [consents3, consentStep, ConsentState.refused, Intim.covers]

/-- After a safeword every act is ruled out until a fresh grant. -/
theorem stop_rules_out (s : ConsentState C) (b a : C) (x : Intim) :
    consents3 (consentStep s (.stop b a)) a b x = .no := by
  simp [consents3, consentStep, ConsentState.refused]

/-- A safeword leaves no grant from the speaker to the partner. -/
theorem stop_removes (s : ConsentState C) (b a : C) (x : Intim) (f : Bool) :
    (consentStep s (.stop b a)).grantFor b a x f = false := by
  simp [consentStep, ConsentState.grantFor, List.any_filter]
  intro g _ h₁ h₂; simp_all

/-- Outside a scene an act needs a firm grant; a blanket offer is not one. -/
theorem no_scene_needs_firm (s : ConsentState C) (a b : C) (x : Intim)
    (h : s.sceneOf a b = none) (hy : consents3 s a b x = .yes) : s.grantFor b a x true = true := by
  unfold consents3 at hy; rw [h] at hy; split at hy <;> simp_all

/-! ## Firsts, and closing scenes -/

/-- Was this `act a b x` the first time `a` or `b` did `x`? (before it is recorded) -/
def ConsentState.firstFor (s : ConsentState C) (c : C) (x : Intim) : Bool :=
  s.never.contains (c, x) && !s.done.any fun (p, q, y) => y == x && (p == c || q == c)

variable [Domain W (ConsentEv C)]

/-- Every first along a story of consent events: (event index, who, act). -/
def firsts : ConsentState C → List (ConsentEv C) → Nat → List (Nat × C × Intim)
  | _, [], _ => []
  | s, e :: es, i =>
    let here := match e with
      | .act a b x => ([a, b].filter (s.firstFor · x)).map (i, ·, x)
      | _ => []
    here ++ firsts (consentStep s e) es (i + 1)

/-- Every scene that ended was closed with aftercare. -/
def ConsentState.cared (s : ConsentState C) : Bool := s.closed.all (·.2)

end LangLib.World
