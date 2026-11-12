import LangLib.World.Space
import LangLib.World.Persona

/-!
# Relationships and consent

Directed bonds between characters on four dimensions (trust, attraction,
affection, tension), each a small natural number. Social events move them;
intimate acts are gated by consent.

* Hard constraint: `act a b x` needs both `a` and `b` present and each to have
  consented to `x` with the other; consent is given by `agree`, and `withdraw`
  takes it back at any time. No persona or bond level overrides this.
* Character: whether someone would `flirt` or `agree` is a defeasible theory
  built from their persona and bonds (shy people hold back, attraction draws
  them on, distrust makes them wary, ...), decided by their value ranking. An
  out-of-character move fails `ok`, and `why` names the blocking rule and the
  setups that would justify it.
* Intimate acts are `Observable` as `SocialFact.did`, so only those present
  know they happened.
-/

namespace LangLib.World
open LangLib.DL

inductive Dim | trust | attraction | affection | tension
  deriving DecidableEq, Repr

/-- Kinds of intimacy, each consented to separately. -/
inductive Act | holdHands | kiss | touch | undress | sex
  deriving DecidableEq, Repr

class HasBonds (W : Type) (C : outParam Type) where
  bond : W → C → C → Dim → Nat
  setBond : W → C → C → Dim → Nat → W
  /-- `(b, a, x)`: `b` consents to `x` with `a` -/
  consent : W → List (C × C × Act)
  setConsent : W → List (C × C × Act) → W

inductive SocialEv (C : Type) where
  | flirt (a b : C)
  | confide (a b : C)
  | argue (a b : C)
  | ask (a b : C) (x : Act)
  | agree (b a : C) (x : Act)
  | withdraw (b a : C) (x : Act)
  | act (a b : C) (x : Act)
  deriving DecidableEq, Repr

inductive SocialFact (C : Type) where
  | did (a b : C) (x : Act)
  deriving DecidableEq, Repr

/-- Atoms of the character theories. -/
inductive SAtom (C : Type) where
  | trait (c : C) (t : Trait)
  | high (c d : C) (k : Dim)
  | low (c d : C) (k : Dim)
  | flirts (c d : C)
  | agrees (c d : C) (x : Act)
  deriving DecidableEq, Repr

variable {W C P : Type} [DecidableEq C] [DecidableEq P]
  [HasLoc W C P] [HasBonds W C] [HasPersona W C]

open HasLoc HasBonds

def bump (w : W) (a b : C) (k : Dim) (n : Int) : W :=
  setBond w a b k (Int.toNat (bond w a b k + n))

def consented (w : W) (b a : C) (x : Act) : Bool := (consent w).contains (b, a, x)

/-- What `c`'s persona and bonds with `d` say, as facts. -/
def socialFacts (w : W) (c d : C) : List (Lit (SAtom C)) :=
  (HasPersona.persona w c).traits.map (fun t => ⟨.trait c t, true⟩) ++
  ([Dim.trust, .attraction, .affection, .tension].flatMap fun k =>
    (if bond w c d k ≥ 2 then [⟨.high c d k, true⟩] else []) ++
    (if bond w c d k == 0 then [⟨.low c d k, true⟩] else []))

def rule (name : String) (v : Option Value) (body : List (SAtom C)) (head : SAtom C)
    (pos : Bool := true) : Rule (SAtom C) Label :=
  { label := { name, value := v }, kind := .defeasible,
    body := body.map (⟨·, true⟩), head := ⟨head, pos⟩ }

def flirtTheory (w : W) (c d : C) : Theory (SAtom C) Label :=
  { facts := socialFacts w c d, sup := valueSup (HasPersona.persona w c),
    rules := [
      rule "shy people hold back" (some .safety) [.trait c .shy] (.flirts c d) false,
      rule "timid people hold back" (some .safety) [.trait c .timid] (.flirts c d) false,
      rule "attraction draws them on" (some .desire) [.high c d .attraction] (.flirts c d),
      rule "the confident make the first move" (some .pride) [.trait c .confident] (.flirts c d),
      rule "no flirting through a grudge" (some .pride) [.high c d .tension] (.flirts c d) false] }

def agreeTheory (w : W) (c d : C) (x : Act) : Theory (SAtom C) Label :=
  { facts := socialFacts w c d, sup := valueSup (HasPersona.persona w c),
    rules := [
      rule "wants them, and trusts them" (some .desire)
        [.high c d .attraction, .high c d .trust] (.agrees c d x),
      rule "no trust, no" (some .safety) [.low c d .trust] (.agrees c d x) false,
      rule "the cautious wait" (some .safety) [.trait c .cautious] (.agrees c d x) false,
      rule "tension sours it" (some .pride) [.high c d .tension] (.agrees c d x) false] }

private def explainChar {α : Type} [DecidableEq α] (T : Theory α Label) (q : Lit α) : String :=
  s!"out of character ({", ".intercalate (blockers T q)}); to justify it, first establish: " ++
    " or ".intercalate (repairs T q)

instance : Domain W (SocialEv C) where
  ok w
    | .flirt a b => loc w a == loc w b && inCharacter (flirtTheory w a b) ⟨.flirts a b, true⟩
    | .confide a b | .argue a b | .ask a b _ => loc w a == loc w b
    | .agree b a x => loc w a == loc w b && inCharacter (agreeTheory w b a x) ⟨.agrees b a x, true⟩
    | .withdraw _ _ _ => true
    | .act a b x => loc w a == loc w b && consented w b a x && consented w a b x
  step w
    | .flirt a b => bump w b a .attraction 1
    | .confide a b => bump (bump w b a .trust 1) a b .affection 1
    | .argue a b => bump (bump (bump (bump w a b .tension 1) b a .tension 1) a b .trust (-1)) b a .trust (-1)
    | .ask _ _ _ => w
    | .agree b a x => setConsent w ((b, a, x) :: consent w)
    | .withdraw b a x => setConsent w ((consent w).filter (· != (b, a, x)))
    | .act a b _ => bump (bump w a b .affection 1) b a .affection 1
  why w
    | .flirt a b => if loc w a != loc w b then "they are not together"
                    else explainChar (flirtTheory w a b) ⟨.flirts a b, true⟩
    | .agree b a x => if loc w a != loc w b then "they are not together"
                      else explainChar (agreeTheory w b a x) ⟨.agrees b a x, true⟩
    | .act a b x =>
      if loc w a != loc w b then "they are not together"
      else if !consented w b a x then "no consent from the partner for this"
      else "no consent from the initiator for this"
    | _ => "they are not together"

instance {Φ : Type} [Inject (SocialFact C) Φ] : Observable W (SocialEv C) Φ P where
  seen w
    | .act a b x => some (loc w a, [ev (SocialFact.did a b x)])
    | _ => none

/-- Who did what with whom is not recorded in the state, so truth here means
"happened" only as far as witnesses believed it; treat it as true. -/
instance : Truth W (SocialFact C) := ⟨fun _ _ => true⟩

end LangLib.World
