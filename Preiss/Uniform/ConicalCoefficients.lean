module
public import Preiss.Uniform.ConicalMoments
public import Preiss.Analysis.AsymptoticCoefficients
public import Mathlib.Tactic

/-! # Sparse Taylor coefficients and support moments of conical measures -/

@[expose] public section
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem gaussianMomentCoefficient_eq_of_exact_homogeneity
    (μ : Measure (Euclidean n)) (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (k d : ℕ) (hk : 0 < k) (hd : 0 < d) (a : MomentForm n k)
    (hf : ∀ s : ℝ, 0 < s → gaussianMomentForm μ k s = s ^ d • a)
    (j : ℕ) (hj : 0 < j) :
    B k j = if j = d then (j.factorial : ℝ) • a else 0 := by
  let A : ℕ → MomentForm n k := fun q => (q.factorial : ℝ)⁻¹ • B k q
  have hA (q : ℕ) (hq : 0 < q) : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => gaussianMomentForm μ k s - ∑ i ∈ Finset.range q, s ^ (i+1) • A (i+1))
      (fun s : ℝ => s ^ q) := by
    convert hB.2 k hk q hq using 1
    funext s
    congr 1
    unfold momentTaylorPolynomial
    apply Finset.sum_congr rfl
    intro i _
    simp only [A, div_eq_mul_inv, smul_smul]
  have heq := taylorCoefficient_eq_of_exact_monomial (gaussianMomentForm μ k) A a d hd hf hA j hj
  have h := congrArg (fun v : MomentForm n k => (j.factorial : ℝ) • v) heq
  have hfac : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  simpa only [A, smul_smul, mul_inv_cancel₀ hfac, one_smul, smul_ite, smul_zero] using h

theorem gaussianMomentCoefficient_conical
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (k j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    B k j = if k = 2*j then (j.factorial : ℝ) • gaussianMomentForm μ k 1 else 0 := by
  rcases Nat.even_or_odd k with heven | hodd
  · obtain ⟨d,hd⟩ := heven
    have hk2 : k = 2*d := by omega
    have hdpos : 0 < d := by omega
    have hf (s : ℝ) (hs : 0 < s) :
        gaussianMomentForm μ k s = s ^ d • gaussianMomentForm μ k 1 := by
      rw [gaussianMomentForm_homogeneous_of_isConical μ hc k s hs]
      have hexp : (k : ℝ)/2 = (d : ℝ) := by rw [hk2]; push_cast; ring
      rw [hexp, Real.rpow_natCast]
    have h := gaussianMomentCoefficient_eq_of_exact_homogeneity μ B hB k d hk hdpos
      (gaussianMomentForm μ k 1) hf j hj
    have heq : (j = d) ↔ k = 2*j := by omega
    simpa only [heq] using h
  · have hf (s : ℝ) (hs : 0 < s) : gaussianMomentForm μ k s = s ^ 1 • (0 : MomentForm n k) := by
      rw [conical_gaussianMoment_odd μ hm hμ hc k hodd s hs, smul_zero]
    have h := gaussianMomentCoefficient_eq_of_exact_homogeneity μ B hB k 1 hk (by decide)
      0 hf j hj
    have hne : k ≠ 2*j := by
      obtain ⟨q,hq⟩ := hodd
      omega
    simpa only [if_neg hne, smul_zero, ite_self] using h

theorem conical_even_moment_on_support
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (j : ℕ) (hj : 0 < j) (x : Euclidean n) (hx : x ∈ μ.support) :
    gaussianMomentForm μ (2*j) 1 (fun _ => x) = ‖x‖ ^ (2*j) / (j.factorial : ℝ) := by
  obtain ⟨B,hB⟩ := exists_gaussianMoment_taylor_coefficients μ hm hμ
  have h := sum_gaussianMomentCoefficient_eq_norm_pow μ hm hμ B hB j hj x hx
  have hsum : (∑ k ∈ Finset.range (2*j), B (k+1) j (fun _ => x)) =
      (j.factorial : ℝ) * gaussianMomentForm μ (2*j) 1 (fun _ => x) := by
    rw [Finset.sum_eq_single (2*j-1)]
    · have hk : 2*j-1+1 = 2*j := by omega
      rw [hk, gaussianMomentCoefficient_conical μ hm hμ hc B hB (2*j) j (by omega) hj,
        if_pos rfl, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    · intro k hk hne
      rw [gaussianMomentCoefficient_conical μ hm hμ hc B hB (k+1) j (by omega) hj,
        if_neg (by omega), ContinuousMultilinearMap.zero_apply]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  rw [hsum] at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))).mpr
  simpa only [mul_comm] using h

end Preiss
