module

public import Preiss.Uniform.MomentForms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Preiss
variable {n : ℕ}

theorem momentBilinear_diag (A : MomentForm n 2) (x : Euclidean n) :
    momentBilinear A x x = A (fun _ => x) := by
  rw [momentBilinear_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem momentBilinear_gaussianMomentForm_symmetric
    (μ : Measure (Euclidean n)) (s : ℝ) (u v : Euclidean n) :
    momentBilinear (gaussianMomentForm μ 2 s) u v =
      momentBilinear (gaussianMomentForm μ 2 s) v u := by
  have h := gaussianMomentForm_permute μ 2 s (Equiv.swap 0 1) (Fin.cons u (fun _ => v))
  have heq : (Fin.cons u (fun _ => v)) ∘ (Equiv.swap (0 : Fin 2) 1) =
      Fin.cons v (fun _ => u) := by
    funext i
    fin_cases i <;> simp [Function.comp_def]
  rw [heq] at h
  simpa only [momentBilinear_apply] using h.symm

theorem integrable_gaussian_inner_sq_of_integrable_momentKernel
    (μ : Measure (Euclidean n))
    (hint : Integrable (fun z => Real.exp (-1 * ‖z‖ ^ 2) • momentKernel 2 z) μ)
    (v : Euclidean n) :
    Integrable (fun z => Real.exp (-‖z‖ ^ 2) * (inner ℝ z v) ^ 2) μ := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
    (fun _ => v)).integrable_comp hint
  simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
    Finset.prod_const] using h

theorem integral_gaussian_inner_sq_eq_momentBilinear
    (μ : Measure (Euclidean n))
    (hint : Integrable (fun z => Real.exp (-1 * ‖z‖ ^ 2) • momentKernel 2 z) μ)
    (hmass : gaussianMass μ 1 ≠ 0) (v : Euclidean n) :
    (∫ z, Real.exp (-‖z‖ ^ 2) * (inner ℝ z v) ^ 2 ∂μ) =
      (gaussianMass μ 1 / 2) * momentBilinear (gaussianMomentForm μ 2 1) v v := by
  rw [momentBilinear_diag]
  have hformula : gaussianMomentForm μ 2 1 (fun _ => v) =
      (2 * (gaussianMass μ 1)⁻¹) *
        (∫ z, Real.exp (-‖z‖ ^ 2) * (inner ℝ z v) ^ 2 ∂μ) := by
    rw [gaussianMomentForm_apply μ 2 1 hint]
    norm_num [gaussianMoment, gaussianMass, Finset.prod_const, mul_comm]
  rw [hformula]
  field_simp [hmass]
  <;> ring

end Preiss
