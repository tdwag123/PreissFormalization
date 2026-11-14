module
public import Preiss.Uniform.MomentCoefficients
public import Preiss.Analysis.AsymptoticCoefficients
public import Mathlib.Analysis.Normed.Operator.Asymptotics

@[expose] public section
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {n : ℕ}

theorem gaussianMomentCoefficient_map_eq_zero_of_lt_growth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure (Euclidean n)) (B : MomentCoefficientFamily n)
    (hB : IsMomentExpansion μ B) (k : ℕ) (hk : 0 < k)
    (L : MomentForm n k →L[ℝ] F) {a : ℝ}
    (hbound : IsBigO (𝓝[>] (0 : ℝ)) (fun s => L (gaussianMomentForm μ k s))
      (fun s : ℝ => s^a)) (j : ℕ) (hj : 0 < j) (hja : (j : ℝ) < a) :
    L (B k j) = 0 := by
  have hexp (q : ℕ) (hq : 0 < q) : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => L (gaussianMomentForm μ k s) -
        ∑ i ∈ Finset.range q, s^(i+1) • (((i+1).factorial : ℝ)⁻¹ • L (B k (i+1))))
      (fun s : ℝ => s^q) := by
    have h := (ContinuousLinearMap.isBigO_comp (𝕜₂ := ℝ) (𝕜₃ := ℝ)
      (F := MomentForm n k) (G := F) L
      (fun s => gaussianMomentForm μ k s - momentTaylorPolynomial B k q s)
      (𝓝[>] (0 : ℝ))).trans_isLittleO (hB.2 k hk q hq)
    simpa only [map_sub, momentTaylorPolynomial, map_sum, map_smul,
      div_eq_mul_inv, mul_smul] using h
  have hz := taylorCoefficient_eq_zero_of_lt_growth
    (fun s => L (gaussianMomentForm μ k s))
    (fun j => (j.factorial : ℝ)⁻¹ • L (B k j)) hbound hexp j hj hja
  exact (smul_eq_zero.mp hz).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)))

theorem gaussianMomentCoefficient_apply_eq_zero_of_lt_growth
    (μ : Measure (Euclidean n)) (B : MomentCoefficientFamily n)
    (hB : IsMomentExpansion μ B) (k : ℕ) (hk : 0 < k)
    (u : Fin k → Euclidean n) {a : ℝ}
    (hbound : IsBigO (𝓝[>] (0 : ℝ)) (fun s => gaussianMomentForm μ k s u)
      (fun s : ℝ => s^a)) (j : ℕ) (hj : 0 < j) (hja : (j : ℝ) < a) :
    B k j u = 0 := by
  exact gaussianMomentCoefficient_map_eq_zero_of_lt_growth μ B hB k hk
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclidean n) ℝ u)
    hbound j hj hja

end Preiss
