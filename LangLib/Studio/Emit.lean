import Lean
import LangLib.Studio.World

/-!
# Checkpoints as data

A story's `Proofs.lean` carries the state after each paragraph as a literal
(`Snap.lean`). Written as a term, a checkpoint is 50–200 KB of syntax, and the
elaborator spends longer on it than the kernel spends on the paragraph's checks
(`abstractions/ROUND-2.md`). `checkpoint% r#"…"#` takes the state as JSON instead,
decodes it, and builds the term directly (`ToExpr`), with raw numerals. Nothing
here is trusted: the kernel checks the definition's type, and `pNN_step` proves
that the paragraph's events reach exactly this state.
-/

namespace LangLib.Studio
open Lean Elab Term Meta LangLib.World

/-- Every state's spec, as a placeholder the elaborator replaces with the
checkpoint's own (`W spec`): the state's terms mention their spec at every
character, place and fact, and a `ToExpr Spec` would copy the spec itself there. -/
private def specVar : FVarId := ⟨`_checkpoint_spec⟩

private local instance : ToExpr Spec := ⟨fun _ => .fvar specVar, mkConst ``Spec⟩

/-- Raw literals: what the kernel reduces fastest, and what elaborating gains nothing over. -/
private local instance (priority := high) : ToExpr Nat := ⟨mkRawNatLit, mkConst ``Nat⟩

deriving instance ToJson, FromJson for Dim
deriving instance ToJson, FromJson for Act
deriving instance ToJson, FromJson for Fact
deriving instance ToJson, FromJson for Ch
deriving instance ToJson, FromJson for Pl
deriving instance ToJson, FromJson for Ob
deriving instance ToJson, FromJson for SFact
deriving instance ToJson, FromJson for EvidKind
deriving instance ToJson, FromJson for Reason
deriving instance ToJson, FromJson for Upgrade
deriving instance ToJson, FromJson for Evid
deriving instance ToJson, FromJson for Belief
deriving instance ToJson, FromJson for Held
deriving instance ToJson, FromJson for SpaceEv
deriving instance ToJson, FromJson for MindEv
deriving instance ToJson, FromJson for SocialEv
deriving instance ToJson, FromJson for DialogueEv
deriving instance ToJson, FromJson for StEv
deriving instance ToJson, FromJson for A
deriving instance ToJson, FromJson for Plan
deriving instance ToJson, FromJson for W

deriving instance ToExpr for Dim
deriving instance ToExpr for Act
deriving instance ToExpr for Fact
deriving instance ToExpr for Ch
deriving instance ToExpr for Pl
deriving instance ToExpr for Ob
deriving instance ToExpr for SFact
deriving instance ToExpr for EvidKind
deriving instance ToExpr for Reason
deriving instance ToExpr for Upgrade
deriving instance ToExpr for Evid
deriving instance ToExpr for Belief
deriving instance ToExpr for Held
deriving instance ToExpr for SpaceEv
deriving instance ToExpr for MindEv
deriving instance ToExpr for SocialEv
deriving instance ToExpr for DialogueEv
deriving instance ToExpr for StEv
deriving instance ToExpr for A
deriving instance ToExpr for Plan
deriving instance ToExpr for W


/-! ## Comparing states

`pNN_step` proves `run cPrev chunk = cNN` by `decide`, so the kernel compares two
states of 50–200 KB. The derived `DecidableEq` carries a proof for every field it
compares (`Eq.rec`, `dite`); a derived `BEq`, lawful by `LawfulBEq`, compares the
same fields with booleans only, and decides the same equation. -/

deriving instance ReflBEq for Fact
deriving instance LawfulBEq for Fact
deriving instance BEq for Ch
deriving instance ReflBEq for Ch
deriving instance LawfulBEq for Ch
deriving instance BEq for Pl
deriving instance ReflBEq for Pl
deriving instance LawfulBEq for Pl
deriving instance BEq for Ob
deriving instance ReflBEq for Ob
deriving instance LawfulBEq for Ob
deriving instance BEq for SFact
deriving instance ReflBEq for SFact
deriving instance LawfulBEq for SFact
deriving instance BEq for Evid
deriving instance ReflBEq for Evid
deriving instance LawfulBEq for Evid
deriving instance BEq for Belief
deriving instance ReflBEq for Belief
deriving instance LawfulBEq for Belief
deriving instance BEq for Held
deriving instance ReflBEq for Held
deriving instance LawfulBEq for Held
deriving instance BEq for SpaceEv
deriving instance ReflBEq for SpaceEv
deriving instance LawfulBEq for SpaceEv
deriving instance BEq for MindEv
deriving instance ReflBEq for MindEv
deriving instance LawfulBEq for MindEv
deriving instance BEq for SocialEv
deriving instance ReflBEq for SocialEv
deriving instance LawfulBEq for SocialEv
deriving instance BEq for DialogueEv
deriving instance ReflBEq for DialogueEv
deriving instance LawfulBEq for DialogueEv
deriving instance BEq for StEv
deriving instance ReflBEq for StEv
deriving instance LawfulBEq for StEv
deriving instance BEq for A
deriving instance ReflBEq for A
deriving instance LawfulBEq for A
deriving instance BEq for Plan
deriving instance ReflBEq for Plan
deriving instance LawfulBEq for Plan
deriving instance BEq for W
deriving instance ReflBEq for W
deriving instance LawfulBEq for W

instance (priority := high) decEqW {s : Spec} : DecidableEq (W s) :=
  fun a b => decidable_of_iff (a == b) beq_iff_eq

/-- A spec with nothing in it: states do not depend on their spec at run time. -/
private def noSpec : Spec := { chars := [], places := [], objects := [], atoms := [] }

/-- The JSON a checkpoint is written as. -/
def checkpointJson {s : Spec} (w : W s) : String := (toJson w).compress

syntax (name := checkpointStx) "checkpoint% " str : term

@[term_elab checkpointStx] def elabCheckpoint : TermElab := fun stx expected? => do
  let `(checkpoint% $j:str) := stx | throwUnsupportedSyntax
  let some ty := expected? | throwError "checkpoint%: the type (`W spec`) must be known"
  let ty ← whnfR ty
  let sE ← match ty.consumeMData with
    | .app (.const ``W _) sE => pure sE
    | _ => throwError "checkpoint%: expected `W spec`, got {ty}"
  match Json.parse j.getString >>= fromJson? (α := W noSpec) with
  | .ok w => return (toExpr w).replaceFVar (.fvar specVar) sE
  | .error e => throwError "checkpoint%: {e}"

end LangLib.Studio
