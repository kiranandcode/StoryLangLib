import LangLib.World.Ties

/-!
# Care: needs, harm, and tending

Hurt/comfort stories turn on care acts that the act set of Social (kiss,
touch, ...) and the moves of Space cannot say: giving someone water, lending
clothes, driving them home, getting them inside, calming them down. Here a
character has *needs* (kinds `K` the story declares: safety, water, warmth,
first aid, comfort, transport, ...). Events:

* `harm x c k`: `x` leaves `c` needing `k` (`x = c` for a fall or a fright);
* `offer a c k`, `accept c a k`, `decline c a k`: care as a proposal, which
  the recipient may take or refuse;
* `tend a c k`: `a` meets `c`'s need `k`: it must exist, the carer is someone
  else, and kinds the story marks as needing consent (`CareLaws.consent`: an
  examination, help undressing) need `c` to have accepted `a`'s offer;
  an implicit acceptance (`acceptQuietly`: not pulling away) counts only for
  kinds marked `implicit`, and is recorded, so a reading says when it leans on it;
* `shield a c x`: `a` puts themself between `x` and `c`: `x` must threaten `c`
  (a relation the story names, `CareLaws.threat`), and `a` comes to protect `c`.

Care builds a tie: `tend a c k` raises the recipient's relation to the carer
that the story names (`CareLaws.builds`, typically trust), by the law-abiding
`setTieLaw` of `Ties.lean`. So whether a later disclosure is in character
(see `Identity.lean`) follows from the care shown before it.

## Registering a need

Care assumed the carer sees the need. Some people do not, for some kinds of
need, in others or in themselves: `CareSight.blind a c k` says `a` does not
register `c`'s need `k` unprompted (`a = c` for one's own). For them a need
registers only when someone points it out (`point b a c k`, by someone who has
registered it) or when the one in need asks for it (`seek c a k`). Until then
they cannot offer or give that care, and cannot ask for it for themselves:
asking for care (`seek`, new here) needs the asker to have registered their own
need. A need registered by being told is known, not felt (`felt`): a story can
make a feeling the felt sign of a need (`Affect.lean`, `signals`), and a blind
character never feels it, though once told she may act on it.

With nobody blind (the default) every old event is allowed exactly as before
(`aware_of_sighted`).
-/

namespace LangLib.World

inductive Consent | none | implicit | explicit
  deriving DecidableEq, Repr

/-- Kinds of need a character does not register unprompted, in someone (or in
themselves): a persona's blind spots. Nobody is blind by default. -/
class CareSight (C K : Type) where
  blind : C → C → K → Bool := fun _ _ _ => false

instance (priority := low) {C K : Type} : CareSight C K := {}

class CareLaws (K : Type) (R : outParam Type) where
  consent : K → Consent := fun _ => .none
  /-- the recipient's tie to the carer that tending raises -/
  builds : Option R := none
  /-- the tie from a threat to its target that shielding answers -/
  threat : Option R := none
  /-- the tie from protector to protected that shielding makes -/
  protects : Option R := none

class HasNeeds (W : Type) (C K : outParam Type) where
  needs : W → C → List K
  setNeeds : W → C → List K → W
  /-- `(c, a, k, explicit)`: `c` has accepted `a`'s offer to tend `k` -/
  accepted : W → List (C × C × K × Bool)
  setAccepted : W → List (C × C × K × Bool) → W
  offers : W → List (C × C × K)
  setOffers : W → List (C × C × K) → W
  /-- `(a, c, k, felt)`: `a` has registered `c`'s need `k`, by noticing it (`felt`) or by being told -/
  registered : W → List (C × C × K × Bool) := fun _ => []
  setRegistered : W → List (C × C × K × Bool) → W := fun w _ => w

inductive CareEv (C K : Type) where
  | harm (x c : C) (k : K)
  | offer (a c : C) (k : K)
  | accept (c a : C) (k : K)
  | acceptQuietly (c a : C) (k : K)
  | decline (c a : C) (k : K)
  | tend (a c : C) (k : K)
  | shield (a c x : C)
  /-- `a` notices `c`'s need `k` (their own, when `a = c`) -/
  | register (a c : C) (k : K)
  /-- `b` points out to `a` that `c` needs `k` -/
  | point (b a c : C) (k : K)
  /-- `c` asks `a` to meet `c`'s need `k` -/
  | seek (c a : C) (k : K)
  deriving DecidableEq, Repr

variable {W C K R : Type} [DecidableEq C] [DecidableEq K] [DecidableEq R]
  [HasNeeds W C K] [HasTies W C R] [TieLaws R] [CareLaws K R] [CareSight C K]

open HasNeeds

def needsNow (w : W) (c : C) (k : K) : Bool := (needs w c).contains k

/-- `a` sees `c`'s need `k`: not blind to it, or it has registered. -/
def aware (w : W) (a c : C) (k : K) : Bool :=
  !CareSight.blind a c k || (registered w).any fun (a', c', k', _) => a' == a && c' == c && k' == k

/-- `a` feels `c`'s need `k` as a need (for one's own: the feeling that signals it):
not blind to it, or noticed it unprompted. Being told is not feeling. -/
def felt (w : W) (a c : C) (k : K) : Bool :=
  !CareSight.blind a c k || (registered w).contains (a, c, k, true)

def addRegistered (w : W) (a c : C) (k : K) (f : Bool) : W :=
  if (registered w).contains (a, c, k, f) then w else setRegistered w ((a, c, k, f) :: registered w)

def consentOk (w : W) (a c : C) (k : K) : Bool :=
  match CareLaws.consent (R := R) k with
  | .none => true
  | .implicit => (accepted w).any fun (c', a', k', _) => c' == c && a' == a && k' == k
  | .explicit => (accepted w).contains (c, a, k, true)

def CareEv.ok (w : W) : CareEv C K → Bool
  | .harm _ _ _ => true
  | .offer a c k => a != c && needsNow w c k && aware w a c k
  | .accept c a k => (offers w).contains (a, c, k)
  | .acceptQuietly c a k => (offers w).contains (a, c, k) && CareLaws.consent (R := R) k == .implicit
  | .decline c a k => (offers w).contains (a, c, k)
  | .tend a c k => a != c && needsNow w c k && consentOk (R := R) w a c k && aware w a c k
  | .shield a c x => a != c && a != x &&
    match CareLaws.threat (K := K) (R := R) with
    | some r => HasTies.tie w r x c > 0
    | none => false
  | .register a c k => needsNow w c k && !CareSight.blind a c k
  | .point b a c k => b != a && needsNow w c k && aware w b c k
  | .seek c a k => c != a && needsNow w c k && aware w c c k

def CareEv.step (w : W) : CareEv C K → W
  | .harm _ c k => if needsNow w c k then w else setNeeds w c (needs w c ++ [k])
  | .offer a c k => setOffers w ((a, c, k) :: offers w)
  | .accept c a k => setAccepted (setOffers w ((offers w).erase (a, c, k))) ((c, a, k, true) :: accepted w)
  | .acceptQuietly c a k =>
    setAccepted (setOffers w ((offers w).erase (a, c, k))) ((c, a, k, false) :: accepted w)
  | .decline c a k => setOffers w ((offers w).erase (a, c, k))
  | .tend a c k =>
    let w := setNeeds w c ((needs w c).erase k)
    let w := setAccepted w ((accepted w).filter fun (c', a', k', _) => !(c' == c && a' == a && k' == k))
    match CareLaws.builds (K := K) (R := R) with
    | some r => setTieLaw w r c a (HasTies.tie w r c a + 1)
    | none => w
  | .shield a c _ =>
    match CareLaws.protects (K := K) (R := R) with
    | some r => setTieLaw w r a c (max 1 (HasTies.tie w r a c))
    | none => w
  | .register a c k => addRegistered w a c k true
  | .point _ a c k => addRegistered w a c k false
  | .seek c a k =>
    let w := addRegistered w a c k false
    setAccepted w ((c, a, k, true) :: accepted w)

instance : Domain W (CareEv C K) where
  ok := CareEv.ok (R := R)
  step := CareEv.step (R := R)
  why w
    | .offer a c k => if a == c then "one cannot offer care to oneself"
                      else if !needsNow w c k then "they do not need that"
                      else if !aware w a c k then "out of character: they do not register this need unprompted; " ++
                        "to justify it, first establish: someone points it out, or the one in need asks" else ""
    | .accept _ _ _ | .decline _ _ _ => "nothing was offered"
    | .acceptQuietly _ _ k =>
      if CareLaws.consent (R := R) k == .explicit then "this kind of care needs a spoken yes"
      else "nothing was offered"
    | .tend a c k =>
      if a == c then "tending oneself is not care from another"
      else if !needsNow w c k then "they do not need that (now)"
      else if !aware w a c k then "out of character: they do not register this need unprompted; " ++
        "to justify it, first establish: someone points it out, or the one in need asks"
      else "this kind of care needs their consent first: an offer, and their acceptance"
    | .shield _ _ _ => "there is no threat to shield them from"
    | .harm _ _ _ => ""
    | .register a c k =>
      if !needsNow w c k then "they do not need that (now)"
      else if a == c then "out of character: they do not register this need in themselves unprompted; " ++
        "to justify it, first establish: someone points it out to them (and even then it is known, not felt)"
      else "out of character: they do not register this need in others unprompted; " ++
        "to justify it, first establish: someone points it out, or the one in need asks"
    | .point b _ c k =>
      if !needsNow w c k then "they do not need that (now)"
      else if !aware w b c k then "the one pointing it out has not registered it themselves"
      else "one cannot point something out to oneself"
    | .seek c a k =>
      if c == a then "asking oneself is not asking" else
      if !needsNow w c k then "they do not need that (now)"
      else "out of character: asking for this needs them to know they need it, and they do not register it " ++
        "in themselves; to justify it, first establish: someone points the need out to them"

/-! ## Laws of sight -/

/-- Where nobody is blind, every need is seen: the old rules, unchanged. -/
theorem aware_of_sighted (w : W) (a c : C) (k : K) (h : CareSight.blind a c k = false) :
    aware w a c k = true := by simp [aware, h]

/-- A blind spot binds: until the need is pointed out (or asked for), no offer. -/
theorem blind_no_offer (w : W) (a c : C) (k : K) (h : aware w a c k = false) :
    CareEv.ok (R := R) w (.offer a c k) = false := by
  simp [CareEv.ok, h]

/-- Nor can one blind to a need of one's own ask for it, until it is pointed out. -/
theorem blind_no_seek (w : W) (c a : C) (k : K) (h : aware w c c k = false) :
    CareEv.ok (R := R) w (.seek c a k) = false := by
  simp [CareEv.ok, h]

/-- Noticing unprompted is ruled out where one is blind, whatever one has been told. -/
theorem blind_no_register (w : W) (a c : C) (k : K) (hb : CareSight.blind a c k = true) :
    CareEv.ok (R := R) w (.register a c k) = false := by
  simp [CareEv.ok, hb]

end LangLib.World
