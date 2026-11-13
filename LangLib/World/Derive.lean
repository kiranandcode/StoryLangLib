import Lean
import LangLib.World.Goals

/-!
# Deriving story instances

A story declares its events and facts as ordinary inductives, one constructor
per module, each constructor taking that module's events (or facts):

```
inductive Fact | space (x : SpaceFact Ch Pl Ob) | social (x : SocialFact Ch)
  deriving DecidableEq, Repr, StoryFact
inductive E | space (x : SpaceEv Ch Pl Ob) | mind (x : MindEv Ch Fact) | social (x : SocialEv Ch)
  deriving DecidableEq, Repr, StoryEvent
```

`deriving StoryFact` generates, for each constructor `c : T → F`, the instance
`Inject T F := ⟨c⟩`, and `Truth`, `Supersedes`, `Fluent` for `F` by dispatch.
`deriving StoryEvent` generates the `Inject`s and `Domain`, `Observable`,
`Purpose` for `E`, each generic in the world and taking the modules' instances
as arguments.

Why not nested `⊕`: for `S₁ ⊕ S₂` an injection can go left or right, so
`Inject` instances overlap and search backtracks; and the composite instance
terms grow past `synthInstance.maxSize`. A named type has exactly one
injection per module and instances that dispatch on constructors, so neither
problem arises.
-/

namespace LangLib.World

/-- Marker: the instances of a story's event type were derived. -/
class StoryEvent (E : Type) : Prop
/-- Marker: the instances of a story's fact type were derived. -/
class StoryFact (F : Type) : Prop

namespace Derive
open Lean Elab Command Term Meta Lean.Parser.Term

/-- Constructors of a story type, each with its single argument's type. -/
def ctorFields (declName : Name) : TermElabM (Array (Name × Term)) := do
  let some (.inductInfo ind) := (← getEnv).find? declName
    | throwError "{declName} is not an inductive type"
  unless ind.numParams == 0 do
    throwError "a story type must not have parameters"
  ind.ctors.toArray.mapM fun c => do
    let some (.ctorInfo ci) := (← getEnv).find? c | throwError "{c} is not a constructor"
    forallTelescopeReducing ci.type fun xs _ => do
      unless xs.size == 1 do
        throwError "{c} must take exactly one argument: a module's events or facts"
      return (c, ← PrettyPrinter.delab (← inferType xs[0]!))

private def alts (fields : Array (Name × Term)) (rhs : Ident → CommandElabM Term) :
    CommandElabM (Array (TSyntax ``Parser.Term.matchAlt)) :=
  fields.mapM fun (c, _) => do
    let x := mkIdent `x
    `(matchAltExpr| | $(mkIdent c):ident $x:ident => $(← rhs x))

def mkEvent (declName : Name) : CommandElabM Unit := do
  let fields ← liftTermElabM (ctorFields declName)
  let E := mkIdent declName
  let (W, Φ, P, C, w) := (mkIdent `W, mkIdent `Φ, mkIdent `P, mkIdent `C, mkIdent `w)
  for (c, t) in fields do
    elabCommand (← `(instance : Inject $t $E := ⟨$(mkIdent c)⟩))
  let dom ← fields.mapM fun (_, t) => `(bracketedBinderF| [Domain $W $t])
  let ok ← alts fields fun x => `(Domain.ok $w $x)
  let ok3 ← alts fields fun x => `(Domain.ok3 $w $x)
  let why ← alts fields fun x => `(Domain.why $w $x)
  let step ← alts fields fun x => `(Domain.step $w $x)
  elabCommand (← `(instance {$W : Type} $dom:bracketedBinder* : Domain $W $E where
    ok := fun $w e => match e with $ok:matchAlt*
    ok3 := fun $w e => match e with $ok3:matchAlt*
    why := fun $w e => match e with $why:matchAlt*
    step := fun $w e => match e with $step:matchAlt*))
  let obs ← fields.mapM fun (_, t) => `(bracketedBinderF| [Observable $W $t $Φ $P])
  let seen ← alts fields fun x => `(Observable.seen $w $x)
  elabCommand (← `(instance {$W $Φ $P : Type} $obs:bracketedBinder* : Observable $W $E $Φ $P where
    seen := fun $w e => match e with $seen:matchAlt*))
  let pur ← fields.mapM fun (_, t) => `(bracketedBinderF| [Purpose $W $t $C $Φ])
  let agent ← alts fields fun x => `(Purpose.agent (W := $W) (C := $C) (Φ := $Φ) $x)
  let eff ← alts fields fun x => `(Purpose.effects (C := $C) $w $x)
  elabCommand (← `(instance {$W $C $Φ : Type} $pur:bracketedBinder* : Purpose $W $E $C $Φ where
    agent := fun e => match e with $agent:matchAlt*
    effects := fun $w e => match e with $eff:matchAlt*))
  elabCommand (← `(instance : StoryEvent $E := ⟨⟩))

def mkFact (declName : Name) : CommandElabM Unit := do
  let fields ← liftTermElabM (ctorFields declName)
  let F := mkIdent declName
  let (W, w) := (mkIdent `W, mkIdent `w)
  for (c, t) in fields do
    elabCommand (← `(instance : Inject $t $F := ⟨$(mkIdent c)⟩))
  let tr ← fields.mapM fun (_, t) => `(bracketedBinderF| [Truth $W $t])
  let truth ← alts fields fun x => `(Truth.truth $w $x)
  elabCommand (← `(instance {$W : Type} $tr:bracketedBinder* : Truth $W $F where
    truth := fun $w f => match f with $truth:matchAlt*))
  let fl ← fields.mapM fun (_, t) => `(bracketedBinderF| [Fluent $t])
  let fluent ← alts fields fun x => `(Fluent.fluent $x)
  elabCommand (← `(instance $fl:bracketedBinder* : Fluent $F where fluent := fun f => match f with $fluent:matchAlt*))
  let sp ← fields.mapM fun (_, t) => `(bracketedBinderF| [Supersedes $t])
  let (a, b) := (mkIdent `a, mkIdent `b)
  let sup ← fields.mapM fun (c, _) =>
    `(matchAltExpr| | $(mkIdent c):ident $a:ident, $(mkIdent c):ident $b:ident => Supersedes.supersedes $a $b)
  elabCommand (← `(instance $sp:bracketedBinder* : Supersedes $F where
    supersedes := fun x y => match x, y with
      $sup:matchAlt*
      | _, _ => false))
  elabCommand (← `(instance : StoryFact $F := ⟨⟩))

initialize
  registerDerivingHandler ``StoryEvent fun names => do
    for n in names do mkEvent n
    return true
  registerDerivingHandler ``StoryFact fun names => do
    for n in names do mkFact n
    return true

end Derive
end LangLib.World
