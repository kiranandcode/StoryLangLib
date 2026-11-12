import LangLib.World.Domain

/-!
# Space: places and objects

Characters are somewhere; objects are held or lie somewhere. Events: `move`,
`take`, `drop`, `give`. Each is visible, as a `SpaceFact`, to everyone in the
place where it happens (`Observable`), which is how a minds module learns.
-/

namespace LangLib.World

/-- Who is where: all a module needs to know who is present. -/
class HasLoc (W : Type) (C P : outParam Type) where
  loc : W → C → P

/-- The finite cast of characters (to find witnesses). -/
class Cast (C : Type) where
  all : List C

class HasSpace (W : Type) (C P O : outParam Type) extends HasLoc W C P where
  setLoc : W → C → P → W
  holder : W → O → Option C
  setHolder : W → O → Option C → W
  objLoc : W → O → P
  setObjLoc : W → O → P → W

/-- What an event shows, and where: `seen w e = some (p, φs)` means everyone at
`p` sees that each `φ` now holds. -/
class Observable (W E Φ P : Type) where
  seen : W → E → Option (P × List Φ)

instance (priority := low) {W E Φ P : Type} : Observable W E Φ P := ⟨fun _ _ => none⟩

instance {W E₁ E₂ Φ P : Type} [Observable W E₁ Φ P] [Observable W E₂ Φ P] :
    Observable W (E₁ ⊕ E₂) Φ P where
  seen w | .inl e => Observable.seen w e | .inr e => Observable.seen w e

/-- Which facts are true in a world. -/
class Truth (W Φ : Type) where
  truth : W → Φ → Bool

instance {W Φ₁ Φ₂ : Type} [Truth W Φ₁] [Truth W Φ₂] : Truth W (Φ₁ ⊕ Φ₂) where
  truth w | .inl φ => Truth.truth w φ | .inr φ => Truth.truth w φ

/-- Learning `new` makes an older belief `old` obsolete (functional facts:
someone is in one place, an object in one place or one hand). -/
class Supersedes (Φ : Type) where
  supersedes : Φ → Φ → Bool

instance (priority := low) {Φ : Type} : Supersedes Φ := ⟨fun _ _ => false⟩

instance {Φ₁ Φ₂ : Type} [Supersedes Φ₁] [Supersedes Φ₂] : Supersedes (Φ₁ ⊕ Φ₂) where
  supersedes
    | .inl a, .inl b => Supersedes.supersedes a b
    | .inr a, .inr b => Supersedes.supersedes a b
    | _, _ => false

/-- Facts that can stop being true (where someone is, who holds what), as
opposed to permanent ones (someone has read the letter). -/
class Fluent (Φ : Type) where
  fluent : Φ → Bool

instance (priority := low) {Φ : Type} : Fluent Φ := ⟨fun _ => false⟩

instance {Φ₁ Φ₂ : Type} [Fluent Φ₁] [Fluent Φ₂] : Fluent (Φ₁ ⊕ Φ₂) where
  fluent | .inl φ => Fluent.fluent φ | .inr φ => Fluent.fluent φ

inductive SpaceEv (C P O : Type) where
  | move (c : C) (p : P)
  | take (c : C) (o : O)
  | drop (c : C) (o : O)
  | give (c d : C) (o : O)
  deriving DecidableEq, Repr

inductive SpaceFact (C P O : Type) where
  | at_ (c : C) (p : P)
  | objAt (o : O) (p : P)
  | holds (c : C) (o : O)
  deriving DecidableEq, Repr

/-! ## What is known

A text rarely says where everyone starts. `PartialLoc` marks whose location is
established; `PartialObj` does the same for objects (where it is and who holds
it). By default everything is known. An event that needs an unknown fact is
`unknown` (not ruled out), and its `step` *assumes* what it needs, making the
fact known: "Mara took the letter" places Mara where the letter was. -/

class PartialLoc (W C : Type) where
  locKnown : W → C → Bool
  /-- `assumeAt w a b`: put `a` where `b` is, and mark it known -/
  assumeAt : W → C → C → W
  markLoc : W → C → W

instance (priority := low) {W C : Type} : PartialLoc W C := ⟨fun _ _ => true, fun w _ _ => w, fun w _ => w⟩

class PartialObj (W O : Type) where
  objKnown : W → O → Bool
  markObj : W → O → W

instance (priority := low) {W O : Type} : PartialObj W O := ⟨fun _ _ => true, fun w _ => w⟩

section
variable {W C P : Type} [DecidableEq C] [DecidableEq P] [HasLoc W C P] [PartialLoc W C]
open HasLoc PartialLoc

/-- Are `a` and `b` in the same place: yes, no, or unknown. -/
def together3 (w : W) (a b : C) : Tri :=
  if locKnown w a && locKnown w b then Tri.ofBool (loc w a == loc w b) else .unknown

/-- Assume `a` and `b` are together, where needed. -/
def meet (w : W) (a b : C) : W :=
  if locKnown w a && locKnown w b then w
  else if locKnown w b then assumeAt w a b
  else assumeAt w b a
end

variable {W C P O : Type} [DecidableEq C] [DecidableEq P] [DecidableEq O] [HasSpace W C P O]
  [PartialLoc W C] [PartialObj W O]

open HasLoc HasSpace PartialLoc PartialObj

/-- Place `c` at `o` (when `c`'s location is unknown) or `o` at `c` (when the
object's is), whichever is unknown, so that `c` can take `o`. -/
private def meetObj (w : W) (c : C) (o : O) : W :=
  let w := if objKnown w o then w else markObj (setHolder (setObjLoc w o (loc w c)) o none) o
  if locKnown w c then w else markLoc (setLoc w c (objLoc w o)) c

instance : Domain W (SpaceEv C P O) where
  ok3 w
    | .move _ _ => .yes
    | .take c o =>
      if !objKnown w o then .unknown
      else if holder w o != none then .no
      else if locKnown w c then Tri.ofBool (objLoc w o == loc w c) else .unknown
    | .drop c o => if objKnown w o then Tri.ofBool (holder w o == some c) else .unknown
    | .give c d o =>
      (if objKnown w o then Tri.ofBool (holder w o == some c) else .unknown).and (together3 w c d)
  ok w e := (match e with
    | .move _ _ => Tri.yes
    | .take c o =>
      if !objKnown w o then .unknown
      else if holder w o != none then .no
      else if locKnown w c then Tri.ofBool (objLoc w o == loc w c) else .unknown
    | .drop c o => if objKnown w o then Tri.ofBool (holder w o == some c) else .unknown
    | .give c d o =>
      (if objKnown w o then Tri.ofBool (holder w o == some c) else .unknown).and (together3 w c d)) == .yes
  step w
    | .move c p => markLoc (setLoc w c p) c
    | .take c o => let w := meetObj w c o; setHolder w o (some c)
    | .drop c o =>
      let w := if objKnown w o then w else markObj (setHolder w o (some c)) o
      setObjLoc (setHolder w o none) o (loc w c)
    | .give c d o =>
      let w := if objKnown w o then w else markObj (setHolder w o (some c)) o
      setHolder (meet w d c) o (some d)
  why w
    | .move _ _ => ""
    | .take c o =>
      if !objKnown w o then "assumes the object was there and unheld"
      else if holder w o != none then "someone already holds it"
      else if !locKnown w c then "assumes they were where it was"
      else "it is not where they are"
    | .drop _ o => if !objKnown w o then "assumes they held it" else "they do not hold it"
    | .give c d o =>
      if !objKnown w o then "assumes they held it"
      else if holder w o != some c then "they do not hold it"
      else if together3 w c d == .unknown then "assumes they were together"
      else "they are not together"

instance : Truth W (SpaceFact C P O) where
  truth w
    | .at_ c p => loc w c == p
    | .objAt o p => holder w o == none && objLoc w o == p
    | .holds c o => holder w o == some c

instance : Supersedes (SpaceFact C P O) where
  supersedes
    | .at_ c _, .at_ c' _ => c == c'
    | .objAt o _, .objAt o' _ => o == o'
    | .objAt o _, .holds _ o' => o == o'
    | .holds _ o, .holds _ o' => o == o'
    | .holds _ o, .objAt o' _ => o == o'
    | _, _ => false

/-- Where people and things are can change. -/
instance : Fluent (SpaceFact C P O) := ⟨fun _ => true⟩

instance {Φ : Type} [Inject (SpaceFact C P O) Φ] : Observable W (SpaceEv C P O) Φ P where
  seen w
    | .move c p => some (p, [ev (SpaceFact.at_ c p : SpaceFact C P O)])
    | .take c o => some (loc w c, [ev (SpaceFact.holds c o : SpaceFact C P O)])
    | .drop c o => some (loc w c, [ev (SpaceFact.objAt o (loc w c) : SpaceFact C P O)])
    | .give _ d o => some (loc w d, [ev (SpaceFact.holds d o : SpaceFact C P O)])

end LangLib.World
