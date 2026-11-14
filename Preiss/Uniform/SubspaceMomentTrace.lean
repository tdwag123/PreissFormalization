module
public import Preiss.Analysis.BilinearTrace
public import Preiss.Uniform.MomentForms
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped BigOperators
namespace Preiss
variable {n : ℕ}

noncomputable def subspaceMomentTraceCLM (U : Submodule ℝ (Euclidean n)) :
    MomentForm n 2 →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ U),
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
      (fun _ => (stdOrthonormalBasis ℝ U i : Euclidean n))

theorem subspaceMomentTraceCLM_apply (U : Submodule ℝ (Euclidean n))
    (A : MomentForm n 2) :
    subspaceMomentTraceCLM U A = bilinearTrace (restrictBilinear (momentBilinear A) U) := by
  rw [bilinearTrace_eq_sum_diagonal _ (stdOrthonormalBasis ℝ U)]
  simp only [subspaceMomentTraceCLM, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  change A (fun _ => (stdOrthonormalBasis ℝ U i : Euclidean n)) =
    A (Fin.cons (stdOrthonormalBasis ℝ U i : Euclidean n)
      (fun _ => (stdOrthonormalBasis ℝ U i : Euclidean n)))
  congr 1
  funext j
  fin_cases j <;> rfl

theorem subspaceMomentTraceCLM_momentKernel (U : Submodule ℝ (Euclidean n))
    (z : Euclidean n) :
    subspaceMomentTraceCLM U (momentKernel 2 z) = ‖U.starProjection z‖ ^ 2 := by
  simp only [subspaceMomentTraceCLM, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.apply_apply, momentKernel_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h := (stdOrthonormalBasis ℝ U).sum_sq_inner_left (U.orthogonalProjectionOnto z)
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at h
  change (∑ i, (inner ℝ z (stdOrthonormalBasis ℝ U i : Euclidean n)) ^ 2) =
    ‖U.starProjection z‖ ^ 2 at h
  exact h

theorem subspaceTrace_gaussianMoment_eq_integral
    (U : Submodule ℝ (Euclidean n)) (μ : Measure (Euclidean n)) (s : ℝ)
    (hint : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel 2 z) μ) :
    subspaceMomentTraceCLM U (gaussianMomentForm μ 2 s) =
      (2 * s^2 * (gaussianMass μ s)⁻¹) *
        ∫ z, Real.exp (-s * ‖z‖ ^ 2) * ‖U.starProjection z‖ ^ 2 ∂μ := by
  rw [gaussianMomentForm, map_smul,
    ← (subspaceMomentTraceCLM U).integral_comp_comm hint]
  simp only [map_smul, subspaceMomentTraceCLM_momentKernel, smul_eq_mul]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  ring

theorem subspaceTrace_gaussianMoment_of_cylinder
    (U : Submodule ℝ (Euclidean n)) (μ : Measure (Euclidean n))
    (b : Euclidean n) (s : ℝ)
    (h1 : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel 1 z) μ)
    (h2 : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel 2 z) μ)
    (hcyl : ∀ᵐ z ∂μ, ‖U.starProjection z‖ ^ 2 = 2 * inner ℝ b z) :
    subspaceMomentTraceCLM U (gaussianMomentForm μ 2 s) =
      2*s * gaussianMomentForm μ 1 s (fun _ => b) := by
  rw [subspaceTrace_gaussianMoment_eq_integral U μ s h2,
    gaussianMomentForm_apply μ 1 s h1]
  have hi : (∫ z, Real.exp (-s * ‖z‖ ^ 2) * ‖U.starProjection z‖ ^ 2 ∂μ) =
      2 * ∫ z, Real.exp (-s * ‖z‖ ^ 2) * inner ℝ z b ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hcyl] with z hz
    rw [hz, real_inner_comm b z]
    ring
  rw [hi]
  simp only [gaussianMoment, gaussianMass, pow_one, Nat.factorial_one,
    Nat.cast_one, div_one, Fin.prod_univ_one]
  simp_rw [mul_comm (inner ℝ _ b)]
  ring

end Preiss
