import LangLib.Studio.Refine

/-!
# Checkpoints: proving a long story without replaying it

`decide +kernel` evaluates closed terms and shares nothing across
declarations, so a theorem about paragraph `k` that restates the story from
its start makes the kernel replay paragraphs `1 … k`: a whole story's
paragraph theorems cost the square of its length. Instead, the generated
`Proofs.lean` (`storyLean`) writes the state after each paragraph down as a
literal (the Studio world is first-order data, `World.lean`) and proves

* `run c₍ₖ₋₁₎ chunkₖ = cₖ`: the paragraph's events, from the previous
  checkpoint, reach this one (one paragraph of kernel work);
* the paragraph's verdicts from `c₍ₖ₋₁₎` (its validity, claims, setting,
  perception, completeness);

and these lemmas chain them into statements about the story from its start,
with no further evaluation.
-/

namespace LangLib.World

variable {W E : Type} [Domain W E] [Perceive W E] [Invariant W] [Clock W]

theorem plausible_append : ∀ (w : W) (es fs : List E),
    Plausible w (es ++ fs) ↔ Plausible w es ∧ Plausible (run w es) fs
  | _, [], _ => ⟨fun h => ⟨.nil, h⟩, fun h => h.2⟩
  | w, e :: es, fs => by
    constructor
    · rintro (_ | ⟨h₁, h₂, h₃⟩)
      have := (plausible_append (next w e) es fs).mp h₃
      exact ⟨.cons h₁ h₂ this.1, this.2⟩
    · rintro ⟨(_ | ⟨h₁, h₂, h₃⟩), h₄⟩
      exact .cons h₁ h₂ ((plausible_append (next w e) es fs).mpr ⟨h₃, h₄⟩)

/-- A valid story up to a checkpoint, then a valid paragraph from it. -/
theorem Valid.chain {w₀ w₁ : W} {es fs : List E} (h₁ : Valid w₀ es) (hr : run w₀ es = w₁)
    (h₂ : Valid w₁ fs) : Valid w₀ (es ++ fs) :=
  (valid_append w₀ es fs).mpr ⟨h₁, hr ▸ h₂⟩

theorem Plausible.chain {w₀ w₁ : W} {es fs : List E} (h₁ : Plausible w₀ es) (hr : run w₀ es = w₁)
    (h₂ : Plausible w₁ fs) : Plausible w₀ (es ++ fs) :=
  (plausible_append w₀ es fs).mpr ⟨h₁, hr ▸ h₂⟩

theorem run_chain {w₀ w₁ w₂ : W} {es fs : List E} (h₁ : run w₀ es = w₁) (h₂ : run w₁ fs = w₂) :
    run w₀ (es ++ fs) = w₂ := by
  rw [run_append, h₁, h₂]

/-- A timed story is valid when its timeline fits and its events, in story-time
order, are a valid sequence. -/
theorem Timed.valid_of {s : Timed E} {w : W} {es : List E}
    (h : s.timeline.length = s.told.length ∧ s.timeline.Satisfies s.constraints ∧
      s.metric.all (·.sat s.timeline) = true)
    (hc : s.chrono = es) (hv : World.Valid w es) : s.Valid w :=
  ⟨h.1, h.2.1, h.2.2, hc ▸ hv⟩

theorem Timed.plausible_of {s : Timed E} {w : W} {es : List E}
    (h : s.timeline.length = s.told.length ∧ s.timeline.Satisfies s.constraints ∧
      s.metric.all (·.sat s.timeline) = true)
    (hc : s.chrono = es) (hv : World.Plausible w es) : s.Plausible w :=
  ⟨h.1, h.2.1, h.2.2, hc ▸ hv⟩

end LangLib.World
