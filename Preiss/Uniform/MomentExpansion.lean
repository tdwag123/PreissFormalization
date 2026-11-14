module

public import Preiss.Uniform.MomentCoefficients
public import Preiss.Uniform.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic.Abel

/-! # Taylor coefficients of uniform-measure moments

These statements are the coefficient-extraction obligations in De Lellis 7.7.
The analytic weighted-projection and finite-feature arguments supply their proofs.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Preiss
variable {n m : ℕ}

/-- Cancellation of a nonvanishing positive-scale monomial in a little-o estimate. -/
theorem eq_zero_of_isLittleO_pow_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (q : ℕ) (a : F)
    (h : Asymptotics.IsLittleO (nhdsWithin 0 (Ioi 0))
      (fun s : ℝ => (s ^ q) • a) (fun s : ℝ => s ^ q)) : a = 0 := by
  have heq : (fun s : ℝ => (s ^ q)⁻¹ • ((s ^ q) • a)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun _ => a) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero q (ne_of_gt hs)), one_smul]
  exact tendsto_nhds_unique tendsto_const_nhds
    (h.tendsto_inv_smul_nhds_zero.congr' heq)

theorem exists_gaussianMoment_taylor_coefficients (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) :
    ∃ B : MomentCoefficientFamily n, IsMomentExpansion μ B := by
  sorry

theorem gaussianMomentCoefficient_unique (μ : Measure (Euclidean n))
    (B C : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (hC : IsMomentExpansion μ C) (k j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    B k j = C k j := by
  revert hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    have hprev (s : ℝ) : momentTaylorPolynomial B k q s = momentTaylorPolynomial C k q s := by
      unfold momentTaylorPolynomial
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (i + 1) (Nat.succ_lt_succ (Finset.mem_range.mp hi)) (Nat.succ_pos i)]
    have hpoly (s : ℝ) :
        momentTaylorPolynomial B k (q + 1) s - momentTaylorPolynomial C k (q + 1) s =
          (s ^ (q + 1) / ((q + 1).factorial : ℝ)) • (B k (q + 1) - C k (q + 1)) := by
      simp only [momentTaylorPolynomial, Finset.sum_range_succ]
      change (momentTaylorPolynomial B k q s +
          (s ^ (q + 1) / ((q + 1).factorial : ℝ)) • B k (q + 1)) -
        (momentTaylorPolynomial C k q s +
          (s ^ (q + 1) / ((q + 1).factorial : ℝ)) • C k (q + 1)) = _
      rw [hprev]
      simp only [smul_sub]
      abel
    have hd := (hC.2 k hk (q + 1) (Nat.succ_pos q)).sub
      (hB.2 k hk (q + 1) (Nat.succ_pos q))
    have hdpoly : Asymptotics.IsLittleO (nhdsWithin 0 (Ioi 0))
        (fun s => momentTaylorPolynomial B k (q + 1) s - momentTaylorPolynomial C k (q + 1) s)
        (fun s : ℝ => s ^ (q + 1)) := by
      convert hd using 1
      funext s
      abel
    have hdscale : Asymptotics.IsLittleO (nhdsWithin 0 (Ioi 0))
        (fun s : ℝ => (s ^ (q + 1)) •
          ((((q + 1).factorial : ℝ)⁻¹) • (B k (q + 1) - C k (q + 1))))
        (fun s : ℝ => s ^ (q + 1)) := by
      convert hdpoly using 1
      funext s
      rw [hpoly, div_eq_mul_inv, mul_smul]
    have hz := eq_zero_of_isLittleO_pow_smul (q + 1)
      ((((q + 1).factorial : ℝ)⁻¹) • (B k (q + 1) - C k (q + 1))) hdscale
    have hfac : (((q + 1).factorial : ℝ)⁻¹) ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hfac)

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
