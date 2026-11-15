import LangLib.World.Relation

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
`setRelLaw` of `Relation.lean`. So whether a later disclosure is in character
(see `Identity.lean`) follows from the care shown before it.
-/

namespace LangLib.World

inductive Consent | none | implicit | explicit
  deriving DecidableEq, Repr

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

inductive CareEv (C K : Type) where
  | harm (x c : C) (k : K)
  | offer (a c : C) (k : K)
  | accept (c a : C) (k : K)
  | acceptQuietly (c a : C) (k : K)
  | decline (c a : C) (k : K)
  | tend (a c : C) (k : K)
  | shield (a c x : C)
  deriving DecidableEq, Repr

variable {W C K R : Type} [DecidableEq C] [DecidableEq K] [DecidableEq R]
  [HasNeeds W C K] [HasRels W C R] [RelLaws R] [CareLaws K R]

open HasNeeds

def needsNow (w : W) (c : C) (k : K) : Bool := (needs w c).contains k

def consentOk (w : W) (a c : C) (k : K) : Bool :=
  match CareLaws.consent (R := R) k with
  | .none => true
  | .implicit => (accepted w).any fun (c', a', k', _) => c' == c && a' == a && k' == k
  | .explicit => (accepted w).contains (c, a, k, true)

def CareEv.ok (w : W) : CareEv C K → Bool
  | .harm _ _ _ => true
  | .offer a c k => a != c && needsNow w c k
  | .accept c a k => (offers w).contains (a, c, k)
  | .acceptQuietly c a k => (offers w).contains (a, c, k) && CareLaws.consent (R := R) k == .implicit
  | .decline c a k => (offers w).contains (a, c, k)
  | .tend a c k => a != c && needsNow w c k && consentOk (R := R) w a c k
  | .shield a c x => a != c && a != x &&
    match CareLaws.threat (K := K) (R := R) with
    | some r => HasRels.rel w r x c > 0
    | none => false

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
    | some r => setRelLaw w r c a (HasRels.rel w r c a + 1)
    | none => w
  | .shield a c _ =>
    match CareLaws.protects (K := K) (R := R) with
    | some r => setRelLaw w r a c (max 1 (HasRels.rel w r a c))
    | none => w

instance : Domain W (CareEv C K) where
  ok := CareEv.ok (R := R)
  step := CareEv.step (R := R)
  why w
    | .offer a c k => if a == c then "one cannot offer care to oneself"
                      else if !needsNow w c k then "they do not need that" else ""
    | .accept _ _ _ | .decline _ _ _ => "nothing was offered"
    | .acceptQuietly _ _ k =>
      if CareLaws.consent (R := R) k == .explicit then "this kind of care needs a spoken yes"
      else "nothing was offered"
    | .tend a c k =>
      if a == c then "tending oneself is not care from another"
      else if !needsNow w c k then "they do not need that (now)"
      else "this kind of care needs their consent first: an offer, and their acceptance"
    | .shield _ _ _ => "there is no threat to shield them from"
    | .harm _ _ _ => ""

end LangLib.World
