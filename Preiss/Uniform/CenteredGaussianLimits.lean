module
public import Preiss.Uniform.MomentCoefficientLimits
public import Preiss.Uniform.MomentExpansion
public import Preiss.Uniform.MomentEstimates
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! # Centered Gaussian moment limits -/

@[expose] public section
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

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
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
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
  simp only [neg_mul] at hmass ⊢
  field_simp [hs'.ne', hmass]
  <;> ring

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
  simp only [neg_mul] at hmass ⊢
  field_simp [hmass, hs'.ne']
  <;> ring

end Preiss
