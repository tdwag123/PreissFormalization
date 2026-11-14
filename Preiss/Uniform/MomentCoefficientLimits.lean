module
public import Preiss.Uniform.MomentCoefficients
public import Preiss.Analysis.TaylorLimits
import Mathlib.Tactic

/-! # Scaled first and second Gaussian moment coefficients -/

@[expose] public section
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem gaussianMoment_first_scaled_limit
    (μ : Measure (Euclidean n)) (B : MomentCoefficientFamily n)
    (hB : IsMomentExpansion μ B) (k : ℕ) (hk : 0 < k) (u : Fin k → Euclidean n) :
    Tendsto (fun s => gaussianMomentForm μ k s u / s) (𝓝[>] (0 : ℝ))
      (𝓝 (B k 1 u)) := by
  have h : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => gaussianMomentForm μ k s - s ^ 1 • B k 1) (fun s : ℝ => s ^ 1) := by
    simpa [momentTaylorPolynomial, Finset.sum_range_succ] using hB.2 k hk 1 (by decide)
  have ht := tendsto_scaled_of_isLittleO_sub _ _ 1 h
  have he := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclidean n) ℝ u).continuous.tendsto
    (B k 1)).comp ht
  simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, pow_one, div_eq_mul_inv, mul_comm] using he

theorem gaussianMoment_second_scaled_limit
    (μ : Measure (Euclidean n)) (B : MomentCoefficientFamily n)
    (hB : IsMomentExpansion μ B) (k : ℕ) (hk : 0 < k) (hzero : B k 1 = 0)
    (u : Fin k → Euclidean n) :
    Tendsto (fun s => gaussianMomentForm μ k s u / s ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (B k 2 u / 2)) := by
  have h : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => gaussianMomentForm μ k s - s ^ 2 • ((1 / 2 : ℝ) • B k 2))
      (fun s : ℝ => s ^ 2) := by
    simpa [momentTaylorPolynomial, Finset.sum_range_succ, hzero, smul_smul, div_eq_mul_inv]
      using hB.2 k hk 2 (by decide)
  have ht := tendsto_scaled_of_isLittleO_sub _ _ 2 h
  have he := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclidean n) ℝ u).continuous.tendsto
    ((1 / 2 : ℝ) • B k 2)).comp ht
  simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, one_mul, one_div, div_eq_mul_inv, mul_comm] using he

end Preiss
