module

public import Preiss.Analysis.GaussianBallPowerParameter
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-! # Polynomially weighted Gaussian integrals bounded by half-scale mass -/

@[expose] public section
open MeasureTheory
namespace Preiss

theorem integral_norm_pow_mul_gaussian_le_halfMass
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ : Measure E) (k : ℕ) (hk : 0 < k) (s : ℝ) (hs : 0 < s)
    (hint : Integrable (fun z => ‖z‖ ^ k * Real.exp (-s * ‖z‖ ^ 2)) μ)
    (hhalf : Integrable (fun z => Real.exp (-(s / 2) * ‖z‖ ^ 2)) μ) :
    (∫ z, ‖z‖ ^ k * Real.exp (-s * ‖z‖ ^ 2) ∂μ) ≤
      ((k : ℝ) / s) ^ ((k : ℝ) / 2) * ∫ z, Real.exp (-(s / 2) * ‖z‖ ^ 2) ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono hint (hhalf.const_mul _)
  intro z
  have he : Real.exp (-s * ‖z‖ ^ 2) =
      Real.exp (-(s / 2) * ‖z‖ ^ 2) * Real.exp (-(s / 2) * ‖z‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_mul_gaussian_half_le (norm_nonneg z) hs k hk)
    (Real.exp_pos _).le

end Preiss
