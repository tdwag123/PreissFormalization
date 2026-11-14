module
public import Preiss.Uniform.MomentCoefficientLimits
public import Preiss.Uniform.MomentEstimates
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! # Gaussian inner products and their first coefficient limits -/
@[expose] public section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem integrable_gaussian_inner_sq_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (s : ℝ) (hs : 0 < s) (u : Euclidean n) :
    Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2) μ := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
    ![u,u]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 2 s hs)
  simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
    Fin.prod_univ_two, pow_two, mul_assoc] using h

theorem integrable_gaussian_inner_sq_centered_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (s : ℝ) (hs : 0 < s) (b u w : Euclidean n) :
    Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 * inner ℝ (z-b) w) μ := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Euclidean n) ℝ
    ![u,u,w]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 3 s hs)
  have h₃ : Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 * inner ℝ z w) μ := by
    simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
      Fin.prod_univ_three, pow_two, mul_assoc] using h
  have h₂ := integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs u
  have hsub : Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 * inner ℝ z w -
      Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 * inner ℝ b w) μ :=
    h₃.sub (h₂.mul_const (inner ℝ b w))
  simpa only [inner_sub_left, mul_sub] using hsub

theorem normalized_gaussian_inner_sq_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B) (u : Euclidean n) :
    Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (B 2 1 ![u,u] / 2)) := by
  have ht := (gaussianMoment_first_scaled_limit μ B hB 2 (by decide) ![u,u]).div_const 2
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  rw [gaussianMomentForm_apply μ 2 s (integrable_gaussianMomentKernel μ hm hμ 2 s hs')]
  simp only [gaussianMoment, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  have hi : (∫ z, (inner ℝ z u * inner ℝ z u) * Real.exp (-s*‖z‖^2) ∂μ) =
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 ∂μ := by
    congr 1
    funext z
    ring
  rw [hi]
  norm_num
  have hmass : gaussianMass μ s ≠ 0 := by
    rw [gaussianMass_unitUniform μ hm hμ s hs']
    exact (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs' _)).ne'
  unfold gaussianMass at hmass ⊢
  simp only [neg_mul] at hmass ⊢
  field_simp [hmass, hs'.ne']
  <;> ring

end Preiss
