module

public import Preiss.Rectifiability.Defs

/-! # Countable carriers and zero-dimensional Hausdorff measure -/

@[expose] public section
open MeasureTheory Set
open scoped NNReal ENNReal

namespace Preiss
variable {X : Type*} [MetricSpace X]

/-- Constant parametrizations cover every countable set, in every dimension. -/
theorem countablyCoveredByLipschitzPieces_of_countable (m : ℕ) {s : Set X}
    (hs : s.Countable) : CountablyCoveredByLipschitzPieces m s := by
  let p : X → LipschitzPiece m X := fun x =>
    { domain := Set.univ
      toFun := fun _ => x
      lipschitz := ⟨0, LipschitzWith.const x⟩ }
  refine ⟨p '' s, hs.image p, ?_⟩
  intro x hx
  exact mem_iUnion₂.mpr ⟨p x, ⟨x, hx, rfl⟩, ⟨⟨0, mem_univ _⟩, rfl⟩⟩

variable [MeasurableSpace X] [BorelSpace X]

theorem countablyRectifiable_of_countable (m : ℕ) {s : Set X}
    (hs : s.Countable) : CountablyRectifiable m s :=
  ⟨s, countablyCoveredByLipschitzPieces_of_countable m hs, by simp⟩

/-- Zero-dimensional Hausdorff measure has no nonempty null sets. -/
theorem absolutelyContinuous_hausdorffMeasure_zero (μ : Measure X) :
    μ ≪ Measure.hausdorffMeasure 0 := by
  intro s hs
  have hempty : s = ∅ := by
    by_contra hne
    have h := Measure.one_le_hausdorffMeasure_zero_of_nonempty (Set.nonempty_iff_ne_empty.mpr hne)
    rw [hs] at h
    exact not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1) h
  simp [hempty]

end Preiss
