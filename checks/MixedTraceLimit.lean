import Preiss.Uniform.CenteredGaussianLimits
import Mathlib.Tactic
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem exists_normalized_norm_sq_centered_gaussian_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B) (b w : Euclidean n) :
    ∃ L : ℝ, Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let A (i : Fin n) := 3 * B 3 2 ![e i,e i,w] - 4 * B 2 1 ![e i,e i] * inner ℝ b w
  have hlim := tendsto_finset_sum Finset.univ (fun i _ =>
    mixed_gaussian_limit_of_moment_expansion μ hm hμ B hB b (e i) w)
  refine ⟨(∑ i, A i) / 8, ?_⟩
  apply (hlim.div_const 8).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  have hint (i : Fin n) : Integrable
      (fun z => Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2 * inner ℝ (z-b) w) μ := by
    have h₃ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Euclidean n) ℝ
      ![e i,e i,w]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 3 s hs')
    have h₂ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
      ![e i,e i]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 2 s hs')
    have hi₃ : Integrable (fun z => Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2 * inner ℝ z w) μ := by
      simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
        Fin.prod_univ_three, pow_two, mul_assoc] using h₃
    have hi₂ : Integrable (fun z => Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2) μ := by
      simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
        Fin.prod_univ_two, pow_two, mul_assoc] using h₂
    apply (hi₃.sub (hi₂.mul_const (inner ℝ b w))).congr
    exact Eventually.of_forall fun z => by simp only [Pi.sub_apply, inner_sub_left, mul_sub]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hint i)]
  have hsum (z : Euclidean n) :
      (∑ i, Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2 * inner ℝ (z-b) w) =
        ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, e.sum_sq_inner_left z]
    ring
  simp_rw [hsum]
  ring

#print axioms exists_normalized_norm_sq_centered_gaussian_limit
end Preiss
