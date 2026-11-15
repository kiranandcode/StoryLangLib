import LangLib.World.Relation

/-!
# Identity: names, pronouns and private facts, as things others know

The base model gives each character one name and one pronoun series, known to
everyone. A story about a trans woman who goes by a nickname needs more:

* a character has several **names** (given, nickname, family, title, coined),
  some of them **private**: shared only with people trusted to a level the
  story sets ("a privilege, like with a trust system");
* each character holds what they know of others' names and **pronouns**, which
  may be missing (a stranger is "they") or wrong (an assumption);
* **private facts** about oneself (being trans) are shared by `disclose`, gated
  by the same trust; learning one any other way (`out`) is allowed, because it
  happens, and recorded as a harm;
* **reference** is an act: `call a b n` (a calls b by name n: a must know it,
  or have coined it), and `refer a b p` (a uses pronoun series p for b). Using a
  series that is not b's is misgendering, recorded with whether a knew better
  (deliberate) or had assumed (mistaken). Nothing is ruled out by being
  cruel; what is ruled out is a name nobody told them.

Trust is a relation of `Relation.lean` (the story names it, `IdentityLaws.trust`),
so care that builds trust (`Care.lean`) is what makes a later disclosure in
character.
-/

namespace LangLib.World

inductive Pron | he | she | they | it
  deriving DecidableEq, Repr

def Pron.ofString? : String → Option Pron
  | "he" => some .he | "she" => some .she | "they" => some .they | "it" => some .it | _ => none

def Pron.name : Pron → String | .he => "he" | .she => "she" | .they => "they" | .it => "it"

inductive NameKind | given | nick | family | title | coined | dead
  deriving DecidableEq, Repr

/-- What a misuse of identity was. -/
inductive IdHarm (C N X : Type) where
  | misgender (a b : C) (p : Pron) (deliberate : Bool)
  | deadname (a b : C) (n : N)
  | outed (a b : C) (x : X)
  deriving DecidableEq, Repr

class IdentityLaws (C N X : Type) (R : outParam Type) where
  pron : C → Pron
  /-- a character's own names, with their kind and the trust needed to be told them -/
  names : C → List (N × NameKind × Nat)
  /-- private facts about a character, with the trust needed to be told them -/
  secrets : C → List (X × Nat)
  trust : Option R

class HasIdent (W : Type) (C N X : outParam Type) where
  /-- `(a, b, n)`: `a` knows `b` goes by `n` (or calls them so) -/
  knownNames : W → List (C × C × N)
  setKnownNames : W → List (C × C × N) → W
  /-- `(a, b, p)`: `a` takes `b`'s pronouns to be `p` -/
  knownPron : W → List (C × C × Pron)
  setKnownPron : W → List (C × C × Pron) → W
  /-- `(a, b, x)`: `a` knows `b`'s private fact `x` -/
  knownSecrets : W → List (C × C × X)
  setKnownSecrets : W → List (C × C × X) → W
  harms : W → List (IdHarm C N X)
  setHarms : W → List (IdHarm C N X) → W

inductive IdEv (C N X : Type) where
  /-- `a` tells `b` that `a` goes by `n` -/
  | introduce (a b : C) (n : N)
  /-- `a` tells `b` that `c` goes by `n` -/
  | tellName (a b c : C) (n : N)
  /-- `a` comes to know `b`'s name `n` some way the text does not show (an assumption) -/
  | learnName (a b : C) (n : N)
  /-- `a` starts calling `b` a name of `a`'s own making -/
  | coin (a b : C) (n : N)
  | call (a b : C) (n : N)
  /-- `a` guesses `b`'s pronouns -/
  | assume (a b : C) (p : Pron)
  /-- `b` tells `a` their pronouns (or gender) -/
  | learnPron (a b : C) (p : Pron)
  /-- `a` tells `b` that `c`'s pronouns are `p` -/
  | tellPron (a b c : C) (p : Pron)
  | refer (a b : C) (p : Pron)
  | disclose (a b : C) (x : X)
  /-- `a` learns `b`'s private fact without `b` sharing it -/
  | out (a b : C) (x : X)
  deriving DecidableEq, Repr

variable {W C N X R : Type} [DecidableEq C] [DecidableEq N] [DecidableEq X] [DecidableEq R]
  [HasIdent W C N X] [IdentityLaws C N X R] [HasRels W C R]

open HasIdent

def knowsName (w : W) (a b : C) (n : N) : Bool :=
  a == b && ((IdentityLaws.names (X := X) (R := R) b).any (·.1 == n)) || (knownNames w).contains (a, b, n)

def pronOf (w : W) (a b : C) : Option Pron :=
  if a == b then some (IdentityLaws.pron N X (R := R) b)
  else ((knownPron w).find? fun (a', b', _) => a' == a && b' == b).map (·.2.2)

def trustOf (w : W) (a b : C) : Nat :=
  match IdentityLaws.trust C N X with
  | some r => HasRels.rel w r a b
  | none => 0

def nameEntry (b : C) (n : N) : Option (N × NameKind × Nat) :=
  (IdentityLaws.names (X := X) (R := R) b).find? (·.1 == n)

def secretNeed (b : C) (x : X) : Option Nat :=
  ((IdentityLaws.secrets N (R := R) b).find? (·.1 == x)).map (·.2)

def addName (w : W) (a b : C) (n : N) : W :=
  if (knownNames w).contains (a, b, n) then w else setKnownNames w ((a, b, n) :: knownNames w)

def setPron (w : W) (a b : C) (p : Pron) : W :=
  setKnownPron w ((a, b, p) :: (knownPron w).filter fun (a', b', _) => !(a' == a && b' == b))

def IdEv.ok (w : W) : IdEv C N X → Bool
  | .introduce a b n => a != b && match nameEntry (X := X) (R := R) a n with
    | some (_, k, need) => k != .dead && trustOf (N := N) (X := X) w a b ≥ need
    | none => false
  | .tellName a b c n => a != b && knowsName (X := X) (R := R) w a c n &&
      ((nameEntry (X := X) (R := R) c n).map (·.2.2 == 0)).getD true
  | .learnName _ b n => (nameEntry (X := X) (R := R) b n).isSome
  | .coin a b _ => a != b
  | .call a b n => knowsName (X := X) (R := R) w a b n
  | .assume a b _ => a != b
  | .learnPron _ b p => p == IdentityLaws.pron N X (R := R) b
  | .tellPron a b c p => a != b && pronOf (N := N) (X := X) (R := R) w a c == some p
  | .refer _ _ _ => true
  | .disclose a b x => a != b && match secretNeed (N := N) (R := R) a x with
    | some need => trustOf (N := N) (X := X) w a b ≥ need
    | none => false
  | .out a b x => a != b && (secretNeed (N := N) (R := R) b x).isSome

def IdEv.step (w : W) : IdEv C N X → W
  | .introduce a b n => addName w b a n
  | .tellName _ b c n => addName w b c n
  | .learnName a b n => addName w a b n
  | .coin a b n => addName (addName w a b n) b b n
  | .call a b n =>
    match nameEntry (X := X) (R := R) b n with
    | some (_, .dead, _) => setHarms w (harms w ++ [.deadname a b n])
    | _ => w
  | .assume a b p => setPron w a b p
  | .learnPron a b p => setPron w a b p
  | .tellPron _ b c p => setPron w b c p
  | .refer a b p =>
    if p == IdentityLaws.pron N X (R := R) b || p == .they then w
    else setHarms w (harms w ++
      [.misgender a b p (pronOf (N := N) (X := X) (R := R) w a b == some (IdentityLaws.pron N X (R := R) b))])
  | .disclose a b x => setKnownSecrets w ((b, a, x) :: knownSecrets w)
  | .out a b x => setHarms (setKnownSecrets w ((a, b, x) :: knownSecrets w)) (harms w ++ [.outed a b x])

instance : Domain W (IdEv C N X) where
  ok := IdEv.ok (R := R)
  step := IdEv.step (R := R)
  why w
    | .introduce a b n => match nameEntry (X := X) (R := R) a n with
      | some (_, .dead, _) => "nobody introduces themself by a name they have left"
      | some (_, _, need) => s!"a private name: shared only with someone trusted to level {need} (trust is {trustOf (N := N) (X := X) w a b})"
      | none => "that is not one of their names"
    | .tellName _ _ _ _ => "they do not know that name, or it is not theirs to share"
    | .learnName _ _ _ => "that is not one of their names"
    | .call _ _ _ => "they use a name nobody has told them"
    | .learnPron _ _ _ => "those are not their pronouns"
    | .tellPron _ _ _ _ => "the speaker does not take those to be their pronouns"
    | .disclose a b _ => s!"a private fact, shared only with someone trusted enough (trust is {trustOf (N := N) (X := X) w a b})"
    | _ => "not allowed"

/-! ## Reference in the text

The prose refers to characters by name and pronoun, and who refers decides what
is allowed: the narrator follows the point-of-view character's knowledge (a
stranger is "they" until she says she is a girl; she is "Deku" only once she
has said so), and a speaker says what *they* know. -/

/-- A reference to `b` in the text: a name, or a pronoun series. -/
inductive Mention (N : Type) where
  | name (n : N)
  | pron (p : Pron)
  deriving DecidableEq, Repr

/-- Is the mention of `b` by `a` (the speaker, or the point of view for the
narrator) one `a` can make? Names: `a` knows it. Pronouns, in narration
(`narr`): the series `a` takes to be `b`'s, or "they" when `a` has none.
Pronouns in speech are free (people misgender), but a series that is not
`b`'s must be read as a `refer` event, so the harm is recorded. -/
def mentionOk (w : W) (narr : Bool) (a b : C) : Mention N → Bool
  | .name n => knowsName (X := X) (R := R) w a b n
  | .pron p =>
    if narr then
      match pronOf (N := N) (X := X) (R := R) w a b with
      | some q => p == q
      | none => p == .they || p == .it
    else true

end LangLib.World
