module

public import Preiss.Uniform.MomentCoefficients
public import Preiss.Uniform.MomentAsymptotics
public import Preiss.Analysis.AsymptoticCoefficients
public import Preiss.Uniform.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic.Abel

/-! # Taylor coefficients of uniform-measure moments

These statements are the coefficient-extraction obligations in De Lellis 7.7.
The analytic weighted-projection and finite-feature arguments supply their proofs.
-/

@[expose] public section
open MeasureTheory Filter Set Asymptotics
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
  have hk : 0 < k := by omega
  have hjk : (j : ℝ) < (k : ℝ) / 2 := by
    have hh : (2 : ℝ) * j < k := by exact_mod_cast hkj
    linarith
  have hz := taylorCoefficient_eq_zero_of_lt_growth (gaussianMomentForm μ k)
    (fun j => ((j.factorial : ℝ)⁻¹) • B k j)
    (gaussianMoment_isBigO_rpow μ hm hμ k hk) (fun q hq => by
      simpa only [momentTaylorPolynomial, div_eq_mul_inv, mul_smul] using hB.2 k hk q hq)
    j hj hjk
  exact (smul_eq_zero.mp hz).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)))

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
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨j, rfl⟩ := hk
  have hpoly (s : ℝ) : momentTaylorPolynomial B (2 * j + 1) (j + 1) s =
      (s ^ (j + 1)) • ((((j + 1).factorial : ℝ)⁻¹) • B (2 * j + 1) (j + 1)) := by
    rw [momentTaylorPolynomial, Finset.sum_range_succ]
    have hz : (∑ i ∈ Finset.range j, (s ^ (i + 1) / ((i + 1).factorial : ℝ)) •
        B (2 * j + 1) (i + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [gaussianMomentCoefficient_eq_zero_of_two_mul_lt μ hm hμ B hB
        (2 * j + 1) (i + 1) (Nat.succ_pos _) (by have := Finset.mem_range.mp hi; omega), smul_zero]
    rw [hz, zero_add, div_eq_mul_inv, mul_smul]
  have hpO : IsBigO (𝓝[>] (0 : ℝ)) (momentTaylorPolynomial B (2 * j + 1) (j + 1))
      (fun s : ℝ => s ^ (j + 1)) := by
    apply IsBigO.of_bound ‖(((j + 1).factorial : ℝ)⁻¹) • B (2 * j + 1) (j + 1)‖
    apply Eventually.of_forall
    intro s
    rw [hpoly, norm_smul, mul_comm]
  have hrem := (hB.2 (2 * j + 1) (by omega) (j + 1) (Nat.succ_pos _)).isBigO
  have hfO : IsBigO (𝓝[>] (0 : ℝ)) (gaussianMomentForm μ (2 * j + 1))
      (fun s : ℝ => s ^ (j + 1)) := by
    convert hrem.add hpO using 1
    funext s
    exact (sub_add_cancel _ _).symm
  have hlo : IsLittleO (𝓝[>] (0 : ℝ)) (gaussianMomentForm μ (2 * j + 1))
      (fun s : ℝ => s ^ (((2 * j + 1 : ℕ) : ℝ) / 2)) := by
    apply hfO.trans_isLittleO
    simpa only [Real.rpow_natCast] using
      (isLittleO_rpow_nhdsGT_zero (a := ((j + 1 : ℕ) : ℝ))
        (b := ((2 * j + 1 : ℕ) : ℝ) / 2) (by push_cast; linarith))
  apply hlo.tendsto_inv_smul_nhds_zero.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [show -((2 * j + 1 : ℕ) : ℝ) / 2 = -(((2 * j + 1 : ℕ) : ℝ) / 2) by ring,
    Real.rpow_neg (le_of_lt (show 0 < s from hs))]

theorem gaussianMoment_scaled_even_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (j : ℕ) (hj : 0 < j) :
    Tendsto (fun s : ℝ => (s ^ j)⁻¹ • gaussianMomentForm μ (2 * j) s)
      (𝓝[>] 0) (𝓝 (((j.factorial : ℝ)⁻¹) • B (2 * j) j)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have hpoly (s : ℝ) : momentTaylorPolynomial B (2 * (q + 1)) (q + 1) s =
      (s ^ (q + 1) / ((q + 1).factorial : ℝ)) • B (2 * (q + 1)) (q + 1) := by
    rw [momentTaylorPolynomial, Finset.sum_range_succ]
    have hz : (∑ i ∈ Finset.range q, (s ^ (i + 1) / ((i + 1).factorial : ℝ)) •
        B (2 * (q + 1)) (i + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [gaussianMomentCoefficient_eq_zero_of_two_mul_lt μ hm hμ B hB
        (2 * (q + 1)) (i + 1) (Nat.succ_pos _) (by have := Finset.mem_range.mp hi; omega), smul_zero]
    rw [hz, zero_add]
  have ht := (hB.2 (2 * (q + 1)) (by omega) (q + 1) (Nat.succ_pos _)).tendsto_inv_smul_nhds_zero
  have hsum := ht.add_const ((((q + 1).factorial : ℝ)⁻¹) • B (2 * (q + 1)) (q + 1))
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hpoly, smul_sub, smul_smul]
  have hpow : s ^ (q + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt (show 0 < s from hs))
  have heq : (s ^ (q + 1))⁻¹ * (s ^ (q + 1) / ((q + 1).factorial : ℝ)) =
      ((q + 1).factorial : ℝ)⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
  rw [heq]
  abel

end Preiss
