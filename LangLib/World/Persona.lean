import LangLib.Story.DL
import LangLib.World.Domain

/-!
# Personas and character checks

A persona is a set of traits and a ranking of values. Modules decide whether an
action is in character by building a small defeasible theory (`LangLib.DL`):
rules that serve a value carry it as their label, and between two such rules
the one serving the value the agent ranks higher wins (`valueSup`).

`inCharacter T q` checks a certificate that `¬q` is refuted (`NotDef T q.neg`),
so an action is ruled out only when the persona positively argues against it;
`motivated T q` checks that `q` itself is defeasibly provable.
-/

namespace LangLib.World
open LangLib.DL

inductive Trait
  | timid | shy | brash | confident | cautious | romantic | loyal | proud
  | dominant | submissive | honest | secretive
  deriving DecidableEq, Repr

inductive Value
  | safety | loyalty | pride | desire | duty | honesty | power | curiosity
  deriving DecidableEq, Repr

structure Persona where
  traits : List Trait
  /-- most preferred first -/
  values : List Value
  deriving Repr

class HasPersona (W : Type) (C : outParam Type) where
  persona : W → C → Persona

def Persona.prefers (p : Persona) (v w : Value) : Bool :=
  match p.values.idxOf? v, p.values.idxOf? w with
  | some i, some j => decide (i < j)
  | some _, none => true
  | _, _ => false

/-- A rule's name and the value it serves. -/
structure Label where
  name : String
  value : Option Value := none
  deriving Repr

/-- Strict rules beat the rest; otherwise the rule serving the more preferred value wins. -/
def valueSup {α : Type} (p : Persona) (t r : Rule α Label) : Bool :=
  (t.kind == .strict && r.kind != .strict) ||
  (t.kind != .strict && r.kind != .strict &&
   match t.label.value, r.label.value with
   | some v, some w => p.prefers v w
   | _, _ => false)

variable {α : Type} [DecidableEq α]

def inCharacter (T : Theory α Label) (q : Lit α) : Bool :=
  let k := certify T
  k.check T && k.steps.contains (q.neg, false)

def motivated (T : Theory α Label) (q : Lit α) : Bool :=
  let k := certify T
  k.check T && k.steps.contains (q, true)

theorem inCharacter_sound (T : Theory α Label) (q : Lit α) (h : inCharacter T q = true) :
    NotDef T q.neg := by
  simp only [inCharacter, Bool.and_eq_true, List.contains_iff_mem] at h
  exact (Cert.sound T _ h.1).2 _ h.2

theorem motivated_sound (T : Theory α Label) (q : Lit α) (h : motivated T q = true) :
    Def T q := by
  simp only [motivated, Bool.and_eq_true, List.contains_iff_mem] at h
  exact (Cert.sound T _ h.1).1 _ h.2

/-- Rules of `T` that fire against `q`, by name: the reason it is out of character. -/
def blockers (T : Theory α Label) (q : Lit α) : List String :=
  let k := certify T
  (T.rules.filter fun r => r.head == q.neg && r.kind != .defeater &&
    r.body.all fun a => k.status a == some true).map (·.label.name)

/-- Rules for `q` that do not yet apply: setups that would justify it. -/
def repairs (T : Theory α Label) (q : Lit α) : List String :=
  let k := certify T
  (T.rules.filter fun r => r.head == q && r.kind != .defeater &&
    !(r.body.all fun a => k.status a == some true)).map (·.label.name)

end LangLib.World
