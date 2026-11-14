module
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! # Vanishing after evaluation of an operator-valued integral

The assertion includes the nonintegrable case, when the total Bochner integral is zero.
-/

open MeasureTheory
namespace Preiss

theorem integral_apply_eq_zero_of_ae {Ω H F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) (A : Ω → H →L[ℝ] F) (u : H)
    (hz : ∀ᵐ z ∂μ, A z u = 0) : (∫ z, A z ∂μ) u = 0 := by
  by_cases hi : Integrable A μ
  · rw [ContinuousLinearMap.integral_apply hi]
    exact integral_eq_zero_of_ae hz
  · rw [integral_undef hi]
    simp

end Preiss
