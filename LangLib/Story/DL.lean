/-!
# Defeasible logic as inductive relations

Ground defeasible logic (Nute; Antoniou, Billington, Governatori & Maher,
"Representation results for defeasible logic", 2001), stated as inductive
relations over an arbitrary atom type:

* `Strict T q` (+Δ): `q` follows from facts by strict rules alone;
* `Def T q` (+∂): `q` is defeasibly provable: some strict or defeasible rule
  for `q` applies, `¬q` is not strictly provable, and every rule for `¬q` is
  either discarded or beaten by an applicable rule for `q` that is superior;
* `NotDef T q` (−∂): `q` is demonstrably not defeasibly provable.

`Rebutted`, `Discarded` and `Unbeaten` are the auxiliary judgements that the
textbook definitions state with `∨`/`∃`; the kernel does not allow those
connectives around a recursive occurrence, so each disjunct is a constructor.

Main results:

* `coherent`: no literal is both `Def` and `NotDef`;
* `Cert.sound`: a certificate accepted by the boolean checker `Cert.check`
  yields `Def`/`NotDef` proofs, so derivations can be found by an untrusted
  evaluator (`certify`) and checked by `decide`.
-/

namespace LangLib.DL

structure Lit (α : Type) where
  atom : α
  pos : Bool := true
  deriving DecidableEq, Repr

def Lit.neg {α} (l : Lit α) : Lit α := { l with pos := !l.pos }

@[simp] theorem Lit.neg_neg {α} (l : Lit α) : l.neg.neg = l := by
  cases l; simp [Lit.neg]

inductive Kind | strict | defeasible | defeater
  deriving DecidableEq, Repr

/-- A rule with a label `L` (a name, or the agent and value it serves). -/
structure Rule (α L : Type) where
  label : L
  kind : Kind
  body : List (Lit α)
  head : Lit α
  deriving DecidableEq, Repr

structure Theory (α L : Type) where
  facts : List (Lit α)
  rules : List (Rule α L)
  /-- `sup t s`: rule `t` overrides rule `s` -/
  sup : Rule α L → Rule α L → Bool

variable {α L : Type}

inductive Strict (T : Theory α L) : Lit α → Prop
  | fact {q} : q ∈ T.facts → Strict T q
  | rule {q} (r : Rule α L) : r ∈ T.rules → r.kind = .strict → r.head = q →
      (∀ a ∈ r.body, Strict T a) → Strict T q

mutual
inductive Def (T : Theory α L) : Lit α → Prop
  | strict {q} : Strict T q → Def T q
  | rule {q} (r : Rule α L) : r ∈ T.rules → r.kind ≠ .defeater → r.head = q →
      (∀ a ∈ r.body, Def T a) → ¬ Strict T q.neg →
      (∀ s ∈ T.rules, s.head = q.neg → Rebutted T q s) → Def T q

/-- The attack of rule `s` on `q` fails. -/
inductive Rebutted (T : Theory α L) : Lit α → Rule α L → Prop
  | discarded {q s} : Discarded T s → Rebutted T q s
  | beaten {q s} (t : Rule α L) : t ∈ T.rules → t.kind ≠ .defeater → t.head = q →
      (∀ a ∈ t.body, Def T a) → T.sup t s = true → Rebutted T q s

/-- Some premise of the rule is refuted. -/
inductive Discarded (T : Theory α L) : Rule α L → Prop
  | mk {r} (a : Lit α) : a ∈ r.body → NotDef T a → Discarded T r

inductive NotDef (T : Theory α L) : Lit α → Prop
  /-- every rule for `q` is discarded -/
  | unsupported {q} : ¬ Strict T q →
      (∀ r ∈ T.rules, r.kind ≠ .defeater → r.head = q → Discarded T r) → NotDef T q
  /-- `¬q` is strictly provable -/
  | contradicted {q} : ¬ Strict T q → Strict T q.neg → NotDef T q
  /-- an applicable rule `s` for `¬q` is overridden by no applicable rule for `q` -/
  | defeated {q} (s : Rule α L) : ¬ Strict T q → s ∈ T.rules → s.head = q.neg →
      (∀ a ∈ s.body, Def T a) →
      (∀ t ∈ T.rules, t.kind ≠ .defeater → t.head = q → Unbeaten T t s) → NotDef T q

/-- Rule `t` for `q` does not override the attacker `s`. -/
inductive Unbeaten (T : Theory α L) : Rule α L → Rule α L → Prop
  | discarded {t s} : Discarded T t → Unbeaten T t s
  | notSup {t s} : T.sup t s = false → Unbeaten T t s
end

/-! ## Notation

Read `T ⊢ …` as "in theory `T`, …".

| notation          | relation          | reading                                   |
|-------------------|-------------------|-------------------------------------------|
| `T ⊢+Δ q`         | `Strict T q`      | `q` follows by strict rules               |
| `T ⊢+∂ q`         | `Def T q`         | `q` is defeasibly provable                |
| `T ⊢−∂ q`         | `NotDef T q`      | `q` is demonstrably not defeasibly provable |
| `T ⊢ s ⇏ q`       | `Rebutted T q s`  | the attack of rule `s` on `q` fails       |
| `T ⊢ r ✗`         | `Discarded T r`   | some premise of rule `r` is refuted       |
| `T ⊢ t ⊁ s`       | `Unbeaten T t s`  | rule `t` does not override rule `s`       |
-/

@[inherit_doc] notation:50 T " ⊢+Δ " q => Strict T q
@[inherit_doc] notation:50 T " ⊢+∂ " q => Def T q
@[inherit_doc] notation:50 T " ⊢−∂ " q => NotDef T q
@[inherit_doc] notation:50 T " ⊢ " s " ⇏ " q => Rebutted T q s
@[inherit_doc] notation:50 T " ⊢ " r " ✗" => Discarded T r
@[inherit_doc] notation:50 T " ⊢ " t " ⊁ " s => Unbeaten T t s

/-! ## Coherence -/

/-- No literal is both defeasibly provable and refuted. -/
theorem coherent (T : Theory α L) : ∀ {q}, (T ⊢+∂ q) → ¬ (T ⊢−∂ q) := by
  intro q hd
  exact @Def.rec α L T
    (fun q _ => ¬ NotDef T q)
    (fun q s _ => (∀ a ∈ s.body, Def T a) →
      (∀ t ∈ T.rules, t.kind ≠ .defeater → t.head = q → Unbeaten T t s) → False)
    (fun r _ => (∀ a ∈ r.body, Def T a) → False)
    (fun q _ => ¬ Def T q)
    (fun t s _ => (∀ a ∈ t.body, Def T a) → T.sup t s = true → False)
    -- Def.strict
    (fun hs hn => by cases hn <;> contradiction)
    -- Def.rule
    (fun r hr hk hh _ hns _ ihBody ihReb hn => by
      cases hn with
      | unsupported _ hdisc =>
        cases hdisc r hr hk hh with
        | mk a ha hna => exact ihBody a ha hna
      | contradicted _ hs => exact hns hs
      | defeated s _ hs hsh hsBody hUnb => exact ihReb s hs hsh hsBody hUnb)
    -- Rebutted.discarded
    (fun _ ih hsBody _ => ih hsBody)
    -- Rebutted.beaten
    (fun t ht htk hth _ hsup ihBody _ hUnb => by
      cases hUnb t ht htk hth with
      | discarded hd => cases hd with | mk a ha hna => exact ihBody a ha hna
      | notSup hf => rw [hsup] at hf; contradiction)
    -- Discarded.mk
    (fun a ha _ ih hBody => ih (hBody a ha))
    -- NotDef.unsupported
    (fun hns _ ihDisc hd => by
      cases hd with
      | strict hs => exact hns hs
      | rule r hr hk hh hBody _ _ => exact ihDisc r hr hk hh hBody)
    -- NotDef.contradicted
    (fun hns hs hd => by
      cases hd with
      | strict h => exact hns h
      | rule _ _ _ _ _ hnn _ => exact hnn hs)
    -- NotDef.defeated
    (fun s hns hs hsh _ _ ihBody ihUnb hd => by
      cases hd with
      | strict h => exact hns h
      | rule r _ _ _ _ _ hreb =>
        cases hreb s hs hsh with
        | discarded hdisc => cases hdisc with | mk a ha hna => exact ihBody a ha hna
        | beaten t ht htk hth htBody hsup => exact ihUnb t ht htk hth htBody hsup)
    -- Unbeaten.discarded
    (fun _ ih htBody _ => ih htBody)
    -- Unbeaten.notSup
    (fun hf _ hsup => by rw [hsup] at hf; contradiction)
    q hd

/-! ## Certificates

A certificate lists the strict closure in derivation order, and a sequence of
`+∂`/`−∂` conclusions each justified by the ones before it. -/

variable [DecidableEq α]

def strictStep (T : Theory α L) (S : List (Lit α)) (q : Lit α) : Bool :=
  T.facts.contains q ||
  T.rules.any fun r => r.kind == .strict && r.head == q && r.body.all S.contains

def strictChain (T : Theory α L) : List (Lit α) → List (Lit α) → Bool
  | _, [] => true
  | done, q :: qs => strictStep T done q && strictChain T (done ++ [q]) qs

/-- `S` contains every fact and is closed under strict rules. -/
def closed (T : Theory α L) (S : List (Lit α)) : Bool :=
  T.facts.all S.contains &&
  T.rules.all fun r => !(r.kind == .strict && r.body.all S.contains) || S.contains r.head

def plusOK (T : Theory α L) (S P M : List (Lit α)) (q : Lit α) : Bool :=
  S.contains q ||
  ((T.rules.any fun r => r.kind != .defeater && r.head == q && r.body.all P.contains) &&
   !S.contains q.neg &&
   T.rules.all fun s => !(s.head == q.neg) || s.body.any M.contains ||
     T.rules.any fun t =>
       t.kind != .defeater && t.head == q && t.body.all P.contains && T.sup t s)

def minusOK (T : Theory α L) (S P M : List (Lit α)) (q : Lit α) : Bool :=
  !S.contains q &&
  ((T.rules.all fun r => !(r.kind != .defeater && r.head == q) || r.body.any M.contains) ||
   S.contains q.neg ||
   T.rules.any fun s => s.head == q.neg && s.body.all P.contains &&
     T.rules.all fun t => !(t.kind != .defeater && t.head == q) ||
       t.body.any M.contains || !T.sup t s)

def stepsOK (T : Theory α L) (S : List (Lit α)) :
    List (Lit α) → List (Lit α) → List (Lit α × Bool) → Bool
  | _, _, [] => true
  | P, M, (q, true) :: rest => plusOK T S P M q && stepsOK T S (P ++ [q]) M rest
  | P, M, (q, false) :: rest => minusOK T S P M q && stepsOK T S P (M ++ [q]) rest

structure Cert (α : Type) where
  strict : List (Lit α)
  steps : List (Lit α × Bool)
  deriving Repr

def Cert.check (T : Theory α L) (c : Cert α) : Bool :=
  strictChain T [] c.strict && closed T c.strict && stepsOK T c.strict [] [] c.steps

theorem strictChain_sound (T : Theory α L) :
    ∀ (L' done : List (Lit α)), strictChain T done L' = true →
      (∀ a ∈ done, Strict T a) → ∀ a ∈ done ++ L', Strict T a := by
  intro L'
  induction L' with
  | nil => intro done _ h a ha; simpa using h a (by simpa using ha)
  | cons q qs ih =>
    intro done hc hd
    simp only [strictChain, Bool.and_eq_true] at hc
    have hq : Strict T q := by
      simp only [strictStep, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
        Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      rcases hc.1 with h | ⟨r, hr, ⟨hk, hh⟩, hb⟩
      · exact .fact h
      · exact .rule r hr hk hh fun a ha => hd a (by simpa using hb a ha)
    have := ih (done ++ [q]) hc.2 (by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with h | rfl
      · exact hd a h
      · exact hq)
    intro a ha
    exact this a (by simpa using ha)

theorem closed_complete (T : Theory α L) (S : List (Lit α)) (hc : closed T S = true) :
    ∀ {q}, Strict T q → q ∈ S := by
  simp only [closed, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hc
  intro q h
  induction h with
  | fact hq => exact hc.1 _ hq
  | rule r hr hk hh _ ih =>
    subst hh
    rcases hc.2 r hr with h | h
    · rcases h with h | h
      · exact absurd hk (by simpa using h)
      · simp only [List.all_eq_false, List.contains_iff_mem] at h
        obtain ⟨a, ha, hn⟩ := h
        exact absurd (ih a ha) (by simpa using hn)
    · exact h

section
variable (T : Theory α L) (S P M : List (Lit α))
  (hS : ∀ {q}, Strict T q ↔ q ∈ S)
  (hP : ∀ a ∈ P, Def T a) (hM : ∀ a ∈ M, NotDef T a)
include hS hP hM

theorem plusOK_sound (q : Lit α) (h : plusOK T S P M q = true) : Def T q := by
  simp only [plusOK, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    List.any_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  rcases h with h | ⟨⟨⟨r, hr, ⟨hk, hh⟩, hb⟩, hneg⟩, hatt⟩
  · exact .strict (hS.2 h)
  · refine .rule r hr hk hh (fun a ha => hP a (hb a ha)) ?_ ?_
    · intro hs; have := hS.1 hs; simp_all
    · intro s hs hsh
      rcases hatt s hs with (h | ⟨a, ha, hm⟩) | ⟨t, ht, ⟨⟨htk, hth⟩, htb⟩, hsup⟩
      · exact absurd hsh (by simpa using h)
      · exact .discarded (.mk a ha (hM a hm))
      · exact .beaten t ht htk hth (fun a ha => hP a (htb a ha)) hsup

theorem minusOK_sound (q : Lit α) (h : minusOK T S P M q = true) : NotDef T q := by
  simp only [minusOK, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem,
    Bool.or_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hnq, h⟩ := h
  have hns : ¬ Strict T q := fun hs => by
    have := hS.1 hs; simp_all
  rcases h with ⟨h | h⟩ | h
  · refine .unsupported hns fun r hr hk hh => ?_
    rcases h r hr with h | ⟨a, ha, hm⟩
    · simp_all
    · exact .mk a ha (hM a hm)
  · exact .contradicted hns (hS.2 h)
  · obtain ⟨s, hs, ⟨hsh, hsb⟩, hall⟩ := h
    refine .defeated s hns hs hsh (fun a ha => hP a (hsb a ha)) fun t ht htk hth => ?_
    rcases hall t ht with (h | ⟨a, ha, hm⟩) | hsup
    · simp [htk, hth] at h
    · exact .discarded (.mk a ha (hM a hm))
    · exact .notSup hsup
end

theorem stepsOK_sound (T : Theory α L) (S : List (Lit α))
    (hS : ∀ {q}, Strict T q ↔ q ∈ S) :
    ∀ (steps : List (Lit α × Bool)) (P M : List (Lit α)),
      (∀ a ∈ P, Def T a) → (∀ a ∈ M, NotDef T a) → stepsOK T S P M steps = true →
      (∀ q, (q, true) ∈ steps → Def T q) ∧ (∀ q, (q, false) ∈ steps → NotDef T q) := by
  intro steps
  induction steps with
  | nil => intro _ _ _ _ _; simp
  | cons st rest ih =>
    obtain ⟨q, b⟩ := st
    intro P M hP hM h
    cases b with
    | true =>
      simp only [stepsOK, Bool.and_eq_true] at h
      have hq := plusOK_sound T S P M hS hP hM q h.1
      have := ih (P ++ [q]) M (by
        intro a ha; simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with h | rfl
        · exact hP a h
        · exact hq) hM h.2
      constructor
      · intro a ha; simp only [List.mem_cons, Prod.mk.injEq] at ha
        rcases ha with ⟨rfl, -⟩ | ha
        · exact hq
        · exact this.1 a ha
      · intro a ha; simp only [List.mem_cons, Prod.mk.injEq] at ha
        rcases ha with ⟨-, h⟩ | ha
        · cases h
        · exact this.2 a ha
    | false =>
      simp only [stepsOK, Bool.and_eq_true] at h
      have hq := minusOK_sound T S P M hS hP hM q h.1
      have := ih P (M ++ [q]) hP (by
        intro a ha; simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with h | rfl
        · exact hM a h
        · exact hq) h.2
      constructor
      · intro a ha; simp only [List.mem_cons, Prod.mk.injEq] at ha
        rcases ha with ⟨-, h⟩ | ha
        · cases h
        · exact this.1 a ha
      · intro a ha; simp only [List.mem_cons, Prod.mk.injEq] at ha
        rcases ha with ⟨rfl, -⟩ | ha
        · exact hq
        · exact this.2 a ha

/-- A checked certificate proves its conclusions. -/
theorem Cert.sound (T : Theory α L) (c : Cert α) (h : c.check T = true) :
    (∀ q, (q, true) ∈ c.steps → Def T q) ∧ (∀ q, (q, false) ∈ c.steps → NotDef T q) := by
  simp only [Cert.check, Bool.and_eq_true] at h
  obtain ⟨⟨hch, hcl⟩, hst⟩ := h
  have hS : ∀ {q}, Strict T q ↔ q ∈ c.strict := fun {q} =>
    ⟨closed_complete T c.strict hcl, fun hq => strictChain_sound T c.strict [] hch (by simp) q (by simpa using hq)⟩
  exact stepsOK_sound T c.strict hS c.steps [] [] (by simp) (by simp) hst

/-! ## Finding certificates

An untrusted evaluator: forward chaining for the strict part, then rounds that
add every literal whose `+∂`/`−∂` condition holds given the conclusions so far.
Literals left undecided (cyclic theories) get no entry. -/

/-- Remove duplicates, keeping first occurrences (structural, so it reduces in proofs). -/
def dedup (l : List (Lit α)) : List (Lit α) :=
  (l.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

/-- Every literal the theory mentions, and its negation. -/
def Theory.literals (T : Theory α L) : List (Lit α) :=
  let ls := T.facts ++ T.rules.flatMap (fun r => r.head :: r.body)
  dedup (ls ++ ls.map Lit.neg)

def strictClosure (T : Theory α L) : Nat → List (Lit α) → List (Lit α)
  | 0, S => S
  | n + 1, S =>
    match T.literals.find? fun q => !S.contains q && strictStep T S q with
    | some q => strictClosure T n (S ++ [q])
    | none => S

def certSteps (T : Theory α L) (S : List (Lit α)) :
    Nat → List (Lit α) → List (Lit α) → List (Lit α × Bool) → List (Lit α × Bool)
  | 0, _, _, acc => acc
  | n + 1, P, M, acc =>
    let open_ := T.literals.filter fun q => !P.contains q && !M.contains q
    match open_.find? (plusOK T S P M), open_.find? (minusOK T S P M) with
    | some q, _ => certSteps T S n (P ++ [q]) M (acc ++ [(q, true)])
    | none, some q => certSteps T S n P (M ++ [q]) (acc ++ [(q, false)])
    | none, none => acc

def certify (T : Theory α L) : Cert α :=
  let n := T.literals.length + 1
  let S := strictClosure T n (dedup T.facts)
  { strict := S, steps := certSteps T S n [] [] [] }

/-- Status of a literal according to a certificate. -/
def Cert.status (c : Cert α) (q : Lit α) : Option Bool :=
  (c.steps.find? (·.1 == q)).map (·.2)

end LangLib.DL
