import Preiss.Uniform.MomentEstimates
import Mathlib.Tactic

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

open MeasureTheory
namespace Preiss
variable {m n : ℕ}

theorem gaussianMass_half_unitUniform (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (s : ℝ) (hs : 0 < s) :
    gaussianMass μ (s / 2) = (2 : ℝ) ^ ((m : ℝ) / 2) * gaussianMass μ s := by
  rw [gaussianMass_unitUniform μ hm hμ (s/2) (half_pos hs),
    gaussianMass_unitUniform μ hm hμ s hs,
    Real.div_rpow hs.le (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  ring

theorem integral_norm_pow_mul_gaussian_le_unitUniform (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (k : ℕ) (hk : 0 < k)
    (s : ℝ) (hs : 0 < s) :
    (∫ z, ‖z‖ ^ k * Real.exp (-s * ‖z‖ ^ 2) ∂μ) ≤
      (2 : ℝ) ^ ((m : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) *
        s ^ (-((k : ℝ) / 2)) * gaussianMass μ s := by
  have hint (j : ℕ) (a : ℝ) (ha : 0 < a) :=
    integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ.1 1 (m : ℝ)
      (IsUnitUniform.hasPolynomialGrowthBound μ hμ) j a ha
  have hhalf : Integrable (fun z : Euclidean n => Real.exp (-(s/2) * ‖z‖ ^ 2)) μ := by
    simpa only [pow_zero, one_mul] using hint 0 (s/2) (half_pos hs)
  have h := integral_norm_pow_mul_gaussian_le_halfMass μ k hk s hs (hint k s hs) hhalf
  change _ ≤ ((k : ℝ) / s) ^ ((k : ℝ) / 2) * gaussianMass μ (s/2) at h
  apply h.trans_eq
  rw [gaussianMass_half_unitUniform μ hm hμ s hs,
    Real.div_rpow (Nat.cast_nonneg k) hs.le, Real.rpow_neg hs.le]
  ring

theorem normalized_gaussian_norm_pow_le_unitUniform (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (k : ℕ) (hk : 0 < k)
    (s : ℝ) (hs : 0 < s) :
    (∫ z, ‖z‖ ^ k * Real.exp (-s * ‖z‖ ^ 2) ∂μ) / gaussianMass μ s ≤
      (2 : ℝ) ^ ((m : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) *
        s ^ (-((k : ℝ) / 2)) := by
  have hmass : 0 < gaussianMass μ s := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)
  exact (div_le_iff₀ hmass).mpr
    (integral_norm_pow_mul_gaussian_le_unitUniform μ hm hμ k hk s hs)

end Preiss


#print axioms Preiss.integral_norm_pow_mul_gaussian_le_halfMass
#print axioms Preiss.gaussianMass_half_unitUniform
#print axioms Preiss.integral_norm_pow_mul_gaussian_le_unitUniform
#print axioms Preiss.normalized_gaussian_norm_pow_le_unitUniform