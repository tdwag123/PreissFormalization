import Preiss.Uniform.FlatAtInfinity.Basic
import Preiss.Uniform.MomentExpansion
import Mathlib.Tactic
open MeasureTheory Filter Set Asymptotics
open scoped Topology
namespace Preiss
variable {m n : ℕ}
theorem tendsto_scaled_of_isLittleO_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (a : F) (k : ℕ)
    (h : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => f s - s ^ k • a) (fun s : ℝ => s ^ k)) :
    Tendsto (fun s => (s ^ k)⁻¹ • f s) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  have ht := h.tendsto_inv_smul_nhds_zero.add_const a
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero k (ne_of_gt hs)), one_smul,
    sub_add_cancel]

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
  simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply,
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
  simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, one_div, div_eq_mul_inv, mul_comm] using he

theorem mixed_gaussian_limit_of_moment_expansion
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (b v w : Euclidean n) :
    Tendsto (fun s : ℝ => (8 * s / gaussianMass μ s) *
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v) ^ 2 *
        inner ℝ (z - b) w ∂μ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (3 * B 3 2 ![v,v,w] - 4 * B 2 1 ![v,v] * inner ℝ b w)) := by
  have h₃ := gaussianMoment_second_scaled_limit μ B hB 3 (by decide)
    (gaussianMomentCoefficient_eq_zero_of_two_mul_lt μ hm hμ B hB 3 1 (by decide) (by decide))
    ![v,v,w]
  have h₂ := gaussianMoment_first_scaled_limit μ B hB 2 (by decide) ![v,v]
  have ht := (h₃.const_mul 6).sub ((h₂.const_mul 4).mul_const (inner ℝ b w))
  have hc : 6 * (B 3 2 ![v,v,w] / 2) = 3 * B 3 2 ![v,v,w] := by ring
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  have hint (k : ℕ) (u : Fin k → Euclidean n) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclidean n) ℝ u).integrable_comp
      (integrable_gaussianMomentKernel μ hm hμ k s hs')
  have hi₃ : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v)^2 * inner ℝ z w) μ := by
    simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
      Fin.prod_univ_three, pow_two, mul_assoc] using hint 3 ![v,v,w]
  have hi₂ : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v)^2) μ := by
    simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
      Fin.prod_univ_two, pow_two, mul_assoc] using hint 2 ![v,v]
  have split : (∫ z, Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v)^2 * inner ℝ (z-b) w ∂μ) =
      (∫ z, Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v)^2 * inner ℝ z w ∂μ) -
      (∫ z, Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v)^2 ∂μ) * inner ℝ b w := by
    simp_rw [inner_sub_left, mul_sub]
    rw [integral_sub hi₃ (hi₂.mul_const _), integral_mul_const]
  rw [split, gaussianMomentForm_apply μ 3 s (integrable_gaussianMomentKernel μ hm hμ 3 s hs'),
    gaussianMomentForm_apply μ 2 s (integrable_gaussianMomentKernel μ hm hμ 2 s hs')]
  simp only [gaussianMoment, Fin.prod_univ_three, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  have swap₃ : (∫ z, inner ℝ z v * inner ℝ z v * inner ℝ z w * Real.exp (-s * ‖z‖ ^ 2) ∂μ) =
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v)^2 * inner ℝ z w ∂μ := by
    congr 1
    funext z
    ring
  have swap₂ : (∫ z, (inner ℝ z v * inner ℝ z v) * Real.exp (-s * ‖z‖ ^ 2) ∂μ) =
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v)^2 ∂μ := by
    congr 1
    funext z
    ring
  rw [swap₃, swap₂]
  norm_num
  have hmass : gaussianMass μ s ≠ 0 := by
    rw [gaussianMass_unitUniform μ hm hμ s hs']
    exact (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs' _)).ne'
  unfold gaussianMass at hmass ⊢
  field_simp [hs'.ne', hmass]
  <;> ring

#print axioms gaussianMoment_first_scaled_limit
#print axioms gaussianMoment_second_scaled_limit
#print axioms mixed_gaussian_limit_of_moment_expansion

theorem normalized_centered_gaussian_limit_of_first_coefficient
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (b w : Euclidean n) (hb : B 1 1 (fun _ => w) = 2 * inner ℝ b w) :
    Tendsto (fun s => (∫ z, inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ) /
      gaussianMass μ s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := ((gaussianMoment_first_scaled_limit μ B hB 1 (by decide) (fun _ => w)).div_const 2).sub_const
    (inner ℝ b w)
  rw [hb, show 2 * inner ℝ b w / 2 - inner ℝ b w = 0 by ring] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  have hi₁ : Integrable (fun z => inner ℝ z w * Real.exp (-s * ‖z‖^2)) μ := by
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euclidean n) ℝ
      (fun _ => w)).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 1 s hs')
    simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
      Fin.prod_univ_one, mul_comm] using h
  have hi₀ : Integrable (fun z : Euclidean n => Real.exp (-s * ‖z‖^2)) μ := by
    simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_gaussian_of_polynomial_growth
      μ hμ.1 1 (m : ℝ) (IsUnitUniform.hasPolynomialGrowthBound μ hμ) 0 s hs'
  have hmass : gaussianMass μ s ≠ 0 := by
    rw [gaussianMass_unitUniform μ hm hμ s hs']
    exact (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs' _)).ne'
  simp_rw [inner_sub_left, sub_mul]
  rw [integral_sub hi₁ (hi₀.const_mul _), integral_const_mul,
    gaussianMomentForm_apply μ 1 s (integrable_gaussianMomentKernel μ hm hμ 1 s hs')]
  simp only [gaussianMoment, Fin.prod_univ_one, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  unfold gaussianMass at hmass ⊢
  field_simp [hmass, hs'.ne']
  <;> ring

#print axioms normalized_centered_gaussian_limit_of_first_coefficient
end Preiss

