module

public import Preiss.Uniform.MomentCoefficients
public import Preiss.Uniform.Defs

/-! # Taylor coefficients of uniform-measure moments

These statements are the coefficient-extraction obligations in De Lellis 7.7.
The analytic weighted-projection and finite-feature arguments supply their proofs.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Preiss
variable {n m : ℕ}

theorem exists_gaussianMoment_taylor_coefficients (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) :
    ∃ B : MomentCoefficientFamily n, IsMomentExpansion μ B := by
  sorry

theorem gaussianMomentCoefficient_unique (μ : Measure (Euclidean n))
    (B C : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (hC : IsMomentExpansion μ C) (k j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    B k j = C k j := by
  sorry

theorem gaussianMomentCoefficient_eq_zero_of_two_mul_lt
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (k j : ℕ) (hj : 0 < j) (hkj : 2 * j < k) : B k j = 0 := by
  sorry

theorem sum_gaussianMomentCoefficient_eq_norm_pow
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (q : ℕ) (hq : 0 < q) (x : Euclidean n) (hx : x ∈ μ.support) :
    (∑ k ∈ Finset.range (2 * q), B (k + 1) q (fun _ => x)) = ‖x‖ ^ (2 * q) := by
  sorry

theorem gaussianMoment_scaled_odd_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (k : ℕ) (hk : Odd k) :
    Tendsto (fun s : ℝ => (s ^ (-(k : ℝ) / 2)) • gaussianMomentForm μ k s)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  sorry

theorem gaussianMoment_scaled_even_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (j : ℕ) (hj : 0 < j) :
    Tendsto (fun s : ℝ => (s ^ j)⁻¹ • gaussianMomentForm μ (2 * j) s)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (((j.factorial : ℝ)⁻¹) • B (2 * j) j)) := by
  sorry

end Preiss
