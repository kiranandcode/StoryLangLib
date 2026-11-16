import LangLib.Studio.World

/-!
# The Studio's record of settled conclusions is exact

`view` reads each character's record of permanent conclusions (`settledT`, L5 in
`abstractions/ROUND-1.md`) where `viewSpec` rebuilds every past view. Here the
Studio world meets `LawfulMinds`, its opening state has right records
(`rec_start`), and every event only learns (`step_grows`); so on every state a
story reaches from `Spec.start`, and in the middle of every event, `view` is
`viewSpec` (`view_run_start`, `view_atStep_start`).
-/

namespace LangLib.Studio
open LangLib.World

variable {s : Spec}

theorem find?_filter_ne {β : Type} (t : List (Nat × β)) (k k' : Nat) (h : k' ≠ k) :
    (t.filter (·.1 != k)).find? (·.1 == k') = t.find? (·.1 == k') := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    by_cases hp : p.1 = k
    · have : (k == k') = false := by simpa using Ne.symm h
      simp [hp, this, ih]
    · simp [hp, List.find?_cons, ih]

theorem tget_tset {β : Type} (t : List (Nat × β)) (k k' : Nat) (v d : β) :
    tget (tset t k v) k' d = if k' = k then v else tget t k' d := by
  unfold tget tset
  by_cases h : k' = k
  · subst h; simp
  · have hk : (k == k') = false := by simpa using Ne.symm h
    simp only [List.find?_cons, hk, find?_filter_ne t k k' h, h, ite_false]

theorem tget_cases {β : Type} (t : List (Nat × β)) (k : Nat) (d : β) :
    tget t k d = d ∨ ∃ p ∈ t, tget t k d = p.2 := by
  unfold tget
  split
  · rename_i a v hf; exact Or.inr ⟨(a, v), List.mem_of_find?_eq_some hf, rfl⟩
  · exact Or.inl rfl

theorem ch_eq_iff (c c' : Ch s) : c' = c ↔ c'.i = c.i := by
  cases c; cases c'; simp

instance : LawfulMinds (W s) (Ch s) (SFact s) where
  beliefs_setBeliefs w c c' bs := by
    show tget (tset w.beliefsT c.i bs) c'.i [] = _
    rw [tget_tset]
    by_cases h : c' = c
    · subst h; simp
    · have : c'.i ≠ c.i := fun e => h ((ch_eq_iff c c').mpr e)
      simp only [h, this, ite_false]; rfl
  settled_setBeliefs _ _ _ _ := rfl
  now_setBeliefs _ _ _ := rfl
  beliefs_setSettled _ _ _ _ := rfl
  settled_setSettled w c c' m m₀ h := by
    have hc : c.i < s.chars.length := by
      show c.i < s.chars.length
      by_cases hc : c.i < s.chars.length
      · exact hc
      · exfalso
        have : HasMinds.settled w c = none := by
          show (if c.i < s.chars.length then some (tget w.settledT c.i []) else none) = none
          simp [hc]
        rw [this] at h; cases h
    show (if c'.i < s.chars.length then some (tget (tset w.settledT c.i m) c'.i []) else none) =
      if c' = c then some m else (if c'.i < s.chars.length then some (tget w.settledT c'.i []) else none)
    by_cases h' : c' = c
    · subst h'; simp [hc, tget_tset]
    · have : c'.i ≠ c.i := fun e => h' ((ch_eq_iff c c').mpr e)
      simp [h', tget_tset, this]
  now_setSettled _ _ _ := rfl
  beliefs_onBetrayal _ _ _ _ := rfl
  settled_onBetrayal _ _ _ _ := rfl
  now_onBetrayal _ _ _ := rfl
  beliefs_tick _ _ := rfl
  settled_tick _ _ := rfl
  now_lt_tick w := Nat.lt_succ_self w.clock

/-! ## The opening state -/

/-- Everyone's opening knowledge is about time 0, the time of the first event, and no
one has a record yet. -/
theorem rec_start (s : Spec) : RecAt (Φ := SFact s) s.start := by
  refine ⟨fun c => ?_, Or.inl rfl⟩
  refine ⟨[], (HasMinds.beliefs s.start c).map Held.plain, rfl, by simp, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    show h.about = 0
    have hb : HasMinds.beliefs s.start c = tget s.start.beliefsT c.i [] := rfl
    rw [hb] at hh
    rcases tget_cases s.start.beliefsT c.i [] with he | ⟨p, hp, he⟩
    · rw [he] at hh; cases hh
    · rw [he] at hh
      obtain ⟨a, _, hfa⟩ := List.mem_filterMap.mp hp
      split at hfa
      · cases hfa
      · cases hfa
        rcases List.mem_append.mp hh with h1 | h1
        · obtain ⟨⟨_, l⟩, _, rfl⟩ := List.mem_map.mp h1
          rfl
        · obtain ⟨⟨_, l, r, e⟩, _, rfl⟩ := List.mem_map.mp h1
          rfl
  · intro m hm
    have hm' : (if c.i < s.chars.length then some (tget ([] : List (Nat × List (SFact s × Bool))) c.i [])
        else none) = some m := hm
    by_cases hc : c.i < s.chars.length
    · simp only [hc, ite_true, Option.some.injEq] at hm'
      subst hm'
      refine ⟨?_, rfl⟩
      show c ∈ (List.range s.chars.length).map (⟨·⟩)
      exact List.mem_map.mpr ⟨c.i, List.mem_range.mpr hc, rfl⟩
    · simp [hc] at hm'

/-! ## Every event only learns -/

/-- A change that leaves the bases, the records and the clock alone. -/
theorem grows_fields {w w' : W s} (hb : w'.beliefsT = w.beliefsT) (hs : w'.settledT = w.settledT)
    (hc : w'.clock = w.clock) : Grows (C := Ch s) (Φ := SFact s) w w' :=
  grows_of_frame hc
    (fun c => by
      show (if c.i < s.chars.length then some (tget w'.settledT c.i []) else none) =
        (if c.i < s.chars.length then some (tget w.settledT c.i []) else none)
      rw [hs])
    (fun c => by show tget w'.beliefsT c.i [] = tget w.beliefsT c.i []; rw [hb])

theorem grows_ite {w a b : W s} {p : Prop} [Decidable p] (ha : Grows (C := Ch s) (Φ := SFact s) w a)
    (hb : Grows (C := Ch s) (Φ := SFact s) w b) : Grows (C := Ch s) (Φ := SFact s) w (if p then a else b) := by
  split
  · exact ha
  · exact hb

theorem meet_grows (w : W s) (a b : Ch s) : Grows (C := Ch s) (Φ := SFact s) w (meet w a b) := by
  unfold meet
  exact grows_ite (Grows.refl w) (grows_ite (grows_fields rfl rfl rfl) (grows_fields rfl rfl rfl))

theorem meetObj_grows (w : W s) (c : Ch s) (o : Ob s) :
    Grows (C := Ch s) (Φ := SFact s) w (meetObj w c o) := by
  unfold meetObj
  simp only []
  refine Grows.trans (w₂ := if PartialObj.objKnown w o then w else PartialObj.markObj
    (HasSpace.setHolder (HasSpace.setObjLoc w o (HasLoc.loc w c)) o none) o)
    (grows_ite (Grows.refl w) (grows_fields rfl rfl rfl)) ?_
  exact grows_ite (Grows.refl _) (grows_fields rfl rfl rfl)

theorem space_grows (w : W s) (x : SpaceEv (Ch s) (Pl s) (Ob s)) :
    Grows (C := Ch s) (Φ := SFact s) w (Domain.step w x) := by
  cases x with
  | move c p => exact grows_fields rfl rfl rfl
  | take c o => exact Grows.trans (meetObj_grows w c o) (grows_fields rfl rfl rfl)
  | drop c o =>
    exact Grows.trans (w₂ := if PartialObj.objKnown w o then w
        else PartialObj.markObj (HasSpace.setHolder w o (some c)) o)
      (grows_ite (Grows.refl w) (grows_fields rfl rfl rfl)) (grows_fields rfl rfl rfl)
  | give c d o =>
    exact Grows.trans (w₂ := if PartialObj.objKnown w o then w
        else PartialObj.markObj (HasSpace.setHolder w o (some c)) o)
      (grows_ite (Grows.refl w) (grows_fields rfl rfl rfl))
      (Grows.trans (meet_grows _ d c) (grows_fields rfl rfl rfl))

theorem mind_grows (w : W s) (x : MindEv (Ch s) (SFact s)) :
    Grows (C := Ch s) (Φ := SFact s) w (Domain.step w x) := by
  cases x with
  | tell c d l =>
    exact Grows.trans (Grows.trans (meet_grows w c d)
      (grows_foldl _ (fun w x => learn_grows w x _ _) _ _)) (learn_grows _ c _ _)
  | whisper c d l =>
    exact Grows.trans (Grows.trans (meet_grows w c d) (learn_grows _ d _ _)) (learn_grows _ c _ _)
  | lie c d l =>
    exact Grows.trans (Grows.trans (meet_grows w c d) (learn_grows _ d _ _)) (learn_grows _ c _ _)
  | message c d l => exact Grows.trans (learn_grows _ d _ _) (learn_grows _ c _ _)
  | notice c l e => exact learn_grows w c _ _
  | realise c l => exact learn_grows w c _ _

theorem social_grows (w : W s) (x : SocialEv (Ch s)) :
    Grows (C := Ch s) (Φ := SFact s) w (Domain.step w x) := by
  cases x with
  | withdraw b a x => exact grows_fields rfl rfl rfl
  | _ => exact Grows.trans (meet_grows w _ _) (grows_fields rfl rfl rfl)

theorem overhear_grows (w : W s) (c d : Ch s) (l : SFact s × Bool) :
    Grows (C := Ch s) (Φ := SFact s) w (overhear w c d l) := by
  unfold overhear
  exact grows_foldl _ (fun w x => learn_grows w x _ _) _ _

theorem dialogue_grows (w : W s) (x : DialogueEv (Ch s) (SFact s)) :
    Grows (C := Ch s) (Φ := SFact s) w (Domain.step w x) := by
  cases x with
  | ask c d φ => exact Grows.trans (meet_grows w c d) (grows_fields rfl rfl rfl)
  | promise c d l => exact Grows.trans (meet_grows w c d) (grows_fields rfl rfl rfl)
  | request c d l => exact Grows.trans (meet_grows w c d) (grows_fields rfl rfl rfl)
  | answer d c l =>
    exact Grows.trans (Grows.trans (Grows.trans (meet_grows w c d)
      (w₃ := HasDialogue.setQuestions (meet w c d)
        ((HasDialogue.questions (meet w c d)).filter (· != (c, d, l.1)))) (grows_fields rfl rfl rfl))
      (learn_grows _ c _ _)) (overhear_grows _ d c l)
  | hint c d l => exact Grows.trans (meet_grows w c d) (learn_grows _ d _ _)
  | sarcasm c d l =>
    exact Grows.trans (Grows.trans (meet_grows w c d) (learn_grows _ d _ _)) (overhear_grows _ c d _)

theorem state_grows (w : W s) (x : StEv s) : Grows (C := Ch s) (Φ := SFact s) w (Domain.step w x) := by
  cases x with
  | make c a v =>
    have g : Grows (C := Ch s) (Φ := SFact s) w (match s.stateWhere a with
        | some p => if w.known.contains c then w else { w with locT := tset w.locT c.i ⟨p⟩, known := c :: w.known }
        | none => w) := by
      split
      · exact grows_ite (Grows.refl w) (grows_fields rfl rfl rfl)
      · exact Grows.refl w
    exact Grows.trans g (grows_fields rfl rfl rfl)
  | become a v => exact grows_fields rfl rfl rfl

/-- Every Studio event only learns: it adds information about the present to bases,
and touches neither the records nor the clock. -/
theorem step_grows (w : W s) (e : E s) : Grows (C := Ch s) (Φ := SFact s) w (Domain.step w e) := by
  cases e with
  | goal x => cases x <;> exact grows_fields rfl rfl rfl
  | action a =>
    cases a with
    | space x => exact space_grows w x
    | mind x => exact mind_grows w x
    | social x => exact social_grows w x
    | dialogue x => exact dialogue_grows w x
    | state x => exact state_grows w x

/-! ## L5 is exact for the Studio -/

/-- Every state a story reaches from the opening has right records. -/
theorem rec_run_start (s : Spec) (es : List (E s)) : RecAt (Φ := SFact s) (run s.start es) :=
  rec_run step_grows s.start es (rec_start s)

/-- On every state a story reaches from the opening, `view` (which reads the record)
is `viewSpec` (which rebuilds every past view). -/
theorem view_run_start (s : Spec) (es : List (E s)) (c : Ch s) :
    view (run s.start es) c = viewSpec (run s.start es) c :=
  view_run step_grows s.start (rec_start s) es c

/-- The states the checks read (`Valid`, `Was`, `Throughout`, the checkpoints of a
proof file): each is `atStep s.start es n`, and there `view` is `viewSpec`. No
validity is needed: it holds for any events. -/
theorem view_atStep_start (s : Spec) (es : List (E s)) (n : Nat) (c : Ch s) :
    view (atStep s.start es n) c = viewSpec (atStep s.start es n) c :=
  view_run_start s (es.take n) c

/-- Within an event too: the views `step` itself builds (the liar check in
`learnWith`, `tell`'s precondition at the next state) are taken on a world that has
only learned since a reachable state, and there `view` is `viewSpec`. -/
theorem view_within_event (s : Spec) (es : List (E s)) {w' : W s}
    (hg : Grows (C := Ch s) (Φ := SFact s) (run s.start es) w') (c : Ch s) :
    view w' c = viewSpec w' c :=
  view_eq_viewSpec_of_grows (rec_run_start s es).1 hg c

/-! ## The counterexamples the exact statement met before the fix

Before `b5d7b97`'s record was fixed, `view` and `viewSpec` differed on these two
worlds (checked with `#eval`); `view_run_start` now proves them equal, and the
checks below run them. -/

namespace RecordCex

/-- A premise known at the opening is revised by the first event. Both are about
time 0 (the clock is 0 until the first event ends), so `viewAt 0` never had the
conclusion; the opening record had it, and the old `view` kept it ("read"). -/
def s₁ : Spec where
  chars := [{ id := "c", name := "C" }]
  places := ["a", "b"]
  objects := []
  atoms := [{ id := "read", label := "read", truth := true }]
  lore := [([(.at_ 0 1, true)], (.atom 0, true))]
  startAt := [(0, 0)]
  knows := [(0, (.at_ 0 1, true))]

def w₁ : W s₁ := run s₁.start [Ev.toE s₁ (.notice 0 (.at_ 0 1, false) .self)]

example : view w₁ (⟨0⟩ : Ch s₁) = viewSpec w₁ ⟨0⟩ := by decide
example : (view w₁ (⟨0⟩ : Ch s₁)).contains (⟨.atom 0⟩, true) = false := by decide

/-- An empty base under lore rules with empty bodies, a changeable head first: the old
`view` added `now`'s heads to the (empty) record, so the permanent head came first. -/
def s₂ : Spec where
  chars := [{ id := "c", name := "C" }]
  places := ["a"]
  objects := []
  atoms := [{ id := "x", label := "x", truth := true }]
  lore := [([], (.at_ 0 0, true)), ([], (.atom 0, true))]

example : view s₂.start (⟨0⟩ : Ch s₂) = viewSpec s₂.start ⟨0⟩ := by decide
example : view s₂.start (⟨0⟩ : Ch s₂) = [(⟨.at_ 0 0⟩, true), (⟨.atom 0⟩, true)] := by decide

end RecordCex

end LangLib.Studio
