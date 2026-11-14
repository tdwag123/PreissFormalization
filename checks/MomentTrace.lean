import Preiss.Analysis.BilinearTrace
import Preiss.Uniform.MomentEstimates
import Preiss.Uniform.MomentCoefficients
import Preiss.Analysis.AsymptoticCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

open MeasureTheory Filter Set Asymptotics
open scoped BigOperators Topology
namespace Preiss
variable {n m : ℕ}

noncomputable def momentTraceCLM (n : ℕ) : MomentForm n 2 →L[ℝ] ℝ :=
  ∑ i : Fin n, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
    (fun _ => EuclideanSpace.basisFun (Fin n) ℝ i)

theorem momentTraceCLM_apply (A : MomentForm n 2) :
    momentTraceCLM n A = bilinearTrace (momentBilinear A) := by
  rw [bilinearTrace_eq_sum_diagonal _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [momentTraceCLM, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.apply_apply, momentBilinear_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem momentTraceCLM_momentKernel (z : Euclidean n) :
    momentTraceCLM n (momentKernel 2 z) = ‖z‖ ^ 2 := by
  simp only [momentTraceCLM, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.apply_apply, momentKernel_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_left z

theorem integral_norm_sq_gaussian_unitUniform (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (s : ℝ) (hs : 0 < s) :
    (∫ z, ‖z‖ ^ 2 * Real.exp (-s * ‖z‖ ^ 2) ∂μ) =
      ((m : ℝ) / (2 * s)) * gaussianMass μ s := by
  have hg := IsUnitUniform.hasPolynomialGrowthBound μ hμ
  have hd : HasDerivAt (gaussianMass μ)
      (-(∫ z, ‖z‖ ^ 2 * Real.exp (-s * ‖z‖ ^ 2) ∂μ)) s := by
    simpa only [MvPolynomial.eval_one, mul_one, one_mul, gaussianMass] using
      hasDerivAt_integral_polynomial_gaussian_of_ball_bound μ 1 (m : ℝ) hg.1 hg.2.2 1 s hs
  have hp := (Real.hasDerivAt_rpow_const (p := -((m : ℝ) / 2))
    (Or.inl hs.ne')).const_mul (Real.Gamma ((m : ℝ) / 2 + 1))
  have heq : gaussianMass μ =ᶠ[𝓝 s]
      (fun t => Real.Gamma ((m : ℝ) / 2 + 1) * t ^ (-((m : ℝ) / 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact gaussianMass_unitUniform μ hm hμ t ht
  have hder := hd.unique (hp.congr_of_eventuallyEq heq)
  have hpow : s ^ (-((m : ℝ) / 2) - 1) = s ^ (-((m : ℝ) / 2)) / s := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  rw [hpow] at hder
  rw [gaussianMass_unitUniform μ hm hμ s hs]
  linear_combination -hder

theorem trace_gaussianMomentForm_two_checked (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (s : ℝ) (hs : 0 < s) :
    bilinearTrace (momentBilinear (gaussianMomentForm μ 2 s)) = (m : ℝ) * s := by
  have hint := integrable_gaussianMomentKernel μ hm hμ 2 s hs
  have hmass : 0 < gaussianMass μ s := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)
  rw [← momentTraceCLM_apply, gaussianMomentForm, map_smul]
  rw [← (momentTraceCLM n).integral_comp_comm hint]
  simp only [map_smul, momentTraceCLM_momentKernel, smul_eq_mul]
  have hswap : (∫ z, Real.exp (-s * ‖z‖ ^ 2) * ‖z‖ ^ 2 ∂μ) =
      ∫ z, ‖z‖ ^ 2 * Real.exp (-s * ‖z‖ ^ 2) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => mul_comm _ _)
  rw [hswap, integral_norm_sq_gaussian_unitUniform μ hm hμ s hs]
  norm_num
  field_simp [hmass.ne', hs.ne']
  <;> ring

end Preiss
#print axioms Preiss.momentTraceCLM
#print axioms Preiss.momentTraceCLM_apply
#print axioms Preiss.momentTraceCLM_momentKernel
#print axioms Preiss.integral_norm_sq_gaussian_unitUniform
#print axioms Preiss.trace_gaussianMomentForm_two_checked
