-- LangLib/Story/DL.lean : defeasible logic as mutually inductive relations
structure Lit (α) where atom : α; pos : Bool          -- q  or  ¬q
inductive Kind | strict | defeasible | defeater
structure Rule (α L) where label : L; kind : Kind; body : List (Lit α); head : Lit α
structure Theory (α L) where
  facts : List (Lit α);  rules : List (Rule α L);  sup : Rule α L → Rule α L → Bool

inductive Strict (T) : Lit α → Prop                     -- +Δ
  | fact : q ∈ T.facts → Strict T q
  | rule (r) : r ∈ T.rules → r.kind = .strict → r.head = q → (∀ a ∈ r.body, Strict T a) → Strict T q

mutual
inductive Def (T) : Lit α → Prop                        -- +∂  defeasibly provable
  | strict : Strict T q → Def T q
  | rule (r) : r ∈ T.rules → r.kind ≠ .defeater → r.head = q → (∀ a ∈ r.body, Def T a) →
      ¬ Strict T q.neg → (∀ s ∈ T.rules, s.head = q.neg → Rebutted T q s) → Def T q
inductive Rebutted (T) : Lit α → Rule α L → Prop        -- attack s on q fails
  | discarded : Discarded T s → Rebutted T q s
  | beaten (t) : t ∈ T.rules → t.kind ≠ .defeater → t.head = q →
      (∀ a ∈ t.body, Def T a) → T.sup t s = true → Rebutted T q s
inductive Discarded (T) : Rule α L → Prop               -- some premise refuted
  | mk (a) : a ∈ r.body → NotDef T a → Discarded T r
inductive NotDef (T) : Lit α → Prop                     -- −∂  provably not derivable
  | unsupported  : ¬ Strict T q → (∀ r ∈ T.rules, r.kind ≠ .defeater → r.head = q → Discarded T r) → NotDef T q
  | contradicted : ¬ Strict T q → Strict T q.neg → NotDef T q
  | defeated (s) : ¬ Strict T q → s ∈ T.rules → s.head = q.neg → (∀ a ∈ s.body, Def T a) →
      (∀ t ∈ T.rules, t.kind ≠ .defeater → t.head = q → Unbeaten T t s) → NotDef T q
inductive Unbeaten (T) : Rule α L → Rule α L → Prop
  | discarded : Discarded T t → Unbeaten T t s
  | notSup : T.sup t s = false → Unbeaten T t s
end

theorem coherent (T) : Def T q → ¬ NotDef T q                    -- no axioms
theorem Cert.sound (T) (c : Cert α) (h : c.check T = true) :
    (∀ q, (q, true) ∈ c.steps → Def T q) ∧ (∀ q, (q, false) ∈ c.steps → NotDef T q)

-- Scene.lean : personas become theories; sup = the agent's value ranking
--   timid people keep quiet   [safety]  : trait c timid                        ⇒ ¬ shouts c d
--   protect a threatened ally [loyalty] : threatens d v, ally c v, near c v   ⇒   shouts c d
--   drink loosens tongues               : drunk c                             ⇝   shouts c d
--   the gagged cannot shout             : gagged c                            →  ¬ shouts c d
