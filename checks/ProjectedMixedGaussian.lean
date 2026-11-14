module
public import Preiss.Uniform.MomentEstimates
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Preiss
variable {n m : ℕ}

theorem sum_mixed_gaussian_eq_projected
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (K : Submodule ℝ (Euclidean n)) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ K) (b w : Euclidean n) (s : ℝ) (hs : 0 < s) :
    (∑ i, (8*s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z (e i : Euclidean n))^2 * inner ℝ (z-b) w ∂μ) =
      8 * ((s / gaussianMass μ s) *
        ∫ z, Real.exp (-s*‖z‖^2) * ‖K.starProjection z‖^2 * inner ℝ (z-b) w ∂μ) := by
  classical
  have hint (i : ι) : Integrable
      (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z (e i : Euclidean n))^2 * inner ℝ (z-b) w) μ := by
    have h₃ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Euclidean n) ℝ
      ![(e i : Euclidean n),(e i : Euclidean n),w]).integrable_comp
      (integrable_gaussianMomentKernel μ hm hμ 3 s hs)
    have h₂ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
      ![(e i : Euclidean n),(e i : Euclidean n)]).integrable_comp
      (integrable_gaussianMomentKernel μ hm hμ 2 s hs)
    have hi₃ : Integrable (fun z => Real.exp (-s*‖z‖^2) *
        (inner ℝ z (e i : Euclidean n))^2 * inner ℝ z w) μ := by
      simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
        Fin.prod_univ_three, pow_two, mul_assoc] using h₃
    have hi₂ : Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z (e i : Euclidean n))^2) μ := by
      simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
        Fin.prod_univ_two, pow_two, mul_assoc] using h₂
    simpa only [inner_sub_left, mul_sub] using hi₃.sub (hi₂.mul_const (inner ℝ b w))
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hint i)]
  have hsq (z : Euclidean n) : (∑ i, (inner ℝ z (e i : Euclidean n))^2) = ‖K.starProjection z‖^2 := by
    simpa only [K.inner_orthogonalProjectionOnto_eq_of_mem_right] using
      e.sum_sq_inner_left (K.orthogonalProjectionOnto z)
  have hsum (z : Euclidean n) :
      (∑ i, Real.exp (-s*‖z‖^2) * (inner ℝ z (e i : Euclidean n))^2 * inner ℝ (z-b) w) =
      Real.exp (-s*‖z‖^2) * ‖K.starProjection z‖^2 * inner ℝ (z-b) w := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsq]
  simp_rw [hsum]
  ring


end Preiss
#print axioms Preiss.sum_mixed_gaussian_eq_projected
