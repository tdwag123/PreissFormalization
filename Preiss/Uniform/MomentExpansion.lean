module

public import Preiss.Uniform.MomentCoefficients
public import Preiss.Uniform.MomentTaylorJets
public import Preiss.Uniform.MomentAsymptotics
public import Preiss.Analysis.AsymptoticCoefficients
public import Preiss.Uniform.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Arith
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
  classical
  have hex (d : ℕ) := exists_coherent_taylor_coefficients_of_finite_jets
    (symmetricGaussianMomentForm μ (d+1))
    (exists_gaussianMoment_finite_jets μ hm hμ d)
  choose A hA using hex
  let B : MomentCoefficientFamily n := fun k j => match k with
    | 0 => 0
    | d+1 => (j.factorial : ℝ) • (A d j : MomentForm n (d+1))
  refine ⟨B,?_,?_⟩
  · intro k j σ u
    cases k with
    | zero => simp [B]
    | succ d =>
      change ((j.factorial : ℝ) • (A d j : MomentForm n (d+1))) (u ∘ σ) =
        ((j.factorial : ℝ) • (A d j : MomentForm n (d+1))) u
      simp only [ContinuousMultilinearMap.smul_apply]
      rw [(A d j).property σ u]
  · intro k hk q hq
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    let S := symmetricContinuousMultilinearSubmodule
      (ι := Fin (d+1)) (E := Euclidean n) (F := ℝ)
    have h := (ContinuousLinearMap.isBigO_comp (𝕜₂ := ℝ) (𝕜₃ := ℝ)
      (F := SymmetricMomentForm n (d+1)) (G := MomentForm n (d+1)) S.subtypeL
      (fun s => symmetricGaussianMomentForm μ (d+1) s -
        ∑ i ∈ Finset.range q,s^(i+1) • A d (i+1)) (𝓝[>] (0 : ℝ))).trans_isLittleO (hA d q hq)
    have hplain : IsLittleO (𝓝[>] (0 : ℝ))
        (fun s => gaussianMomentForm μ (d+1) s -
          ∑ i ∈ Finset.range q,s^(i+1) • (A d (i+1) : MomentForm n (d+1)))
        (fun s : ℝ => s^q) := by
      simpa only [map_sub,map_sum,map_smul,Submodule.subtypeL_apply,
        symmetricGaussianMomentForm] using h
    have hpoly (s : ℝ) : momentTaylorPolynomial B (d+1) q s =
        ∑ i ∈ Finset.range q,s^(i+1) • (A d (i+1) : MomentForm n (d+1)) := by
      unfold momentTaylorPolynomial
      apply Finset.sum_congr rfl
      intro i _
      change (s^(i+1)/((i+1).factorial : ℝ)) •
        (((i+1).factorial : ℝ) • (A d (i+1) : MomentForm n (d+1))) = _
      rw [smul_smul,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    simpa only [hpoly] using hplain

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
  revert hq
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    let S (s : ℝ) := ∑ k ∈ Finset.range (2 * (p + 1)), gaussianMomentForm μ (k + 1) s (fun _ => x)
    let U (s : ℝ) := ∑ k ∈ Finset.range (2 * (p + 1)), momentTaylorPolynomial B (k + 1) (p + 1) s (fun _ => x)
    let T (s : ℝ) := ∑ j ∈ Finset.range (p + 1), s ^ (j + 1) * ‖x‖ ^ (2 * (j + 1)) / ((j + 1).factorial : ℝ)
    let c (j : ℕ) := ∑ k ∈ Finset.range (2 * (p + 1)), B (k + 1) j (fun _ => x)
    have hSU : IsLittleO (𝓝[>] (0 : ℝ)) (fun s => S s - U s) (fun s : ℝ => s ^ (p + 1)) := by
      have hterm (k : ℕ) : IsLittleO (𝓝[>] (0 : ℝ))
          (fun s => gaussianMomentForm μ (k + 1) s (fun _ => x) -
            momentTaylorPolynomial B (k + 1) (p + 1) s (fun _ => x))
          (fun s : ℝ => s ^ (p + 1)) := by
        let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k + 1) => Euclidean n) ℝ (fun _ => x)
        have h := (ev.isBigO_comp
          (fun s => gaussianMomentForm μ (k + 1) s - momentTaylorPolynomial B (k + 1) (p + 1) s)
          (𝓝[>] (0 : ℝ))).trans_isLittleO (hB.2 (k + 1) (Nat.succ_pos _) (p + 1) (Nat.succ_pos _))
        simpa only [ev, ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.sub_apply] using h
      have hsum := IsLittleO.sum (s := Finset.range (2 * (p + 1))) (fun k _ => hterm k)
      convert hsum using 1
      funext s
      simp only [Finset.sum_apply, Finset.sum_sub_distrib, S, U]
    obtain ⟨C, hC, hbound⟩ := gaussianMoment_taylor_remainder (n := n) hm (p + 1) (Nat.succ_pos _)
    have hSTO : IsBigO (𝓝[>] (0 : ℝ)) (fun s => S s - T s)
        (fun s : ℝ => s ^ (((p + 1 : ℕ) : ℝ) + 1 / 2)) := by
      apply IsBigO.of_bound (C * (‖x‖ ^ 2) ^ (((p + 1 : ℕ) : ℝ) + 1 / 2))
      filter_upwards [self_mem_nhdsWithin] with s hs
      calc
        ‖S s - T s‖ ≤ C * (s * ‖x‖ ^ 2) ^ (((p + 1 : ℕ) : ℝ) + 1 / 2) :=
          hbound μ hμ x hx s hs
        _ = _ := by
          rw [Real.mul_rpow (le_of_lt (show 0 < s from hs)) (sq_nonneg _),
            Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt (show 0 < s from hs)) _)]
          ring
    have hST : IsLittleO (𝓝[>] (0 : ℝ)) (fun s => S s - T s) (fun s : ℝ => s ^ (p + 1)) := by
      simpa only [Real.rpow_natCast] using
        hSTO.trans_isLittleO (isLittleO_rpow_nhdsGT_zero (b := ((p + 1 : ℕ) : ℝ)) (by linarith))
    have hUT : IsLittleO (𝓝[>] (0 : ℝ)) (fun s => U s - T s) (fun s : ℝ => s ^ (p + 1)) := by
      convert hST.sub hSU using 1
      funext s
      ring
    have hc (j : ℕ) (hj : 0 < j) (hjp : j < p + 1) : c j = ‖x‖ ^ (2 * j) := by
      have hsum : (∑ k ∈ Finset.range (2 * j), B (k + 1) j (fun _ => x)) = c j := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro k hk hkj
        have hklarge : 2 * j ≤ k := Nat.le_of_not_gt (fun h => hkj (Finset.mem_range.mpr h))
        rw [gaussianMomentCoefficient_eq_zero_of_two_mul_lt μ hm hμ B hB (k + 1) j hj (by omega)]
        simp
      rw [← hsum]
      exact ih j hjp hj
    have hU (s : ℝ) : U s = ∑ j ∈ Finset.range (p + 1),
        (s ^ (j + 1) / ((j + 1).factorial : ℝ)) * c (j + 1) := by
      dsimp only [U, momentTaylorPolynomial, c]
      simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    have hpoly (s : ℝ) : U s - T s = (s ^ (p + 1)) •
        ((((p + 1).factorial : ℝ)⁻¹) * (c (p + 1) - ‖x‖ ^ (2 * (p + 1)))) := by
      rw [hU]
      dsimp only [T]
      rw [← Finset.sum_sub_distrib, Finset.sum_range_succ]
      have hz : (∑ j ∈ Finset.range p,
          ((s ^ (j + 1) / ((j + 1).factorial : ℝ)) * c (j + 1) -
            s ^ (j + 1) * ‖x‖ ^ (2 * (j + 1)) / ((j + 1).factorial : ℝ))) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hc (j + 1) (Nat.succ_pos _) (Nat.succ_lt_succ (Finset.mem_range.mp hj))]
        ring
      rw [hz, zero_add, smul_eq_mul]
      ring
    have hz : (((p + 1).factorial : ℝ)⁻¹) * (c (p + 1) - ‖x‖ ^ (2 * (p + 1))) = 0 := by
      apply eq_zero_of_isLittleO_pow_smul (p + 1)
      simpa only [hpoly] using hUT
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))))

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
