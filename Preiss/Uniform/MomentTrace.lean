module
public import Preiss.Analysis.BilinearTrace
public import Preiss.Uniform.MomentEstimates
public import Preiss.Uniform.MomentCoefficients
public import Preiss.Analysis.AsymptoticCoefficients
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic

/-! # Gaussian second-moment trace and coefficient trace identities -/

@[expose] public section
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
    have h := hasDerivAt_integral_polynomial_gaussian_of_ball_bound μ 1 (m : ℝ)
      hg.1 hg.2.2 (1 : MvPolynomial (Fin n) ℝ) s hs
    simp only [map_one, mul_one, one_mul] at h
    exact h
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

theorem trace_gaussianMomentForm_two (μ : Measure (Euclidean n))
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

theorem trace_secondMomentCoefficient_eq_zero
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B) :
    bilinearTrace (momentBilinear (B 2 2)) = 0 := by
  have herror (q : ℕ) (hq : 0 < q) : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => momentTraceCLM n (gaussianMomentForm μ 2 s - momentTaylorPolynomial B 2 q s))
      (fun s : ℝ => s ^ q) :=
    (ContinuousLinearMap.isBigO_comp (𝕜₂ := ℝ) (𝕜₃ := ℝ)
      (F := MomentForm n 2) (G := ℝ) (momentTraceCLM n)
      (fun s => gaussianMomentForm μ 2 s - momentTaylorPolynomial B 2 q s)
      (𝓝[>] (0 : ℝ))).trans_isLittleO (hB.2 2 (by decide) q hq)
  have hfirst : momentTraceCLM n (B 2 1) = (m : ℝ) := by
    have hsmall : IsLittleO (𝓝[>] (0 : ℝ))
        (fun s : ℝ => s ^ 1 • ((m : ℝ) - momentTraceCLM n (B 2 1)))
        (fun s : ℝ => s ^ 1) := by
      apply (herror 1 (by decide)).congr' ?_ (Filter.EventuallyEq.refl _ _)
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [map_sub, momentTraceCLM_apply (gaussianMomentForm μ 2 s),
        trace_gaussianMomentForm_two μ hm hμ s hs]
      simp only [momentTaylorPolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, map_add, map_smul, map_zero, smul_eq_mul]
      norm_num
      <;> ring
    have hz := eq_zero_of_isLittleO_pow_smul 1
      ((m : ℝ) - momentTraceCLM n (B 2 1)) hsmall
    linarith
  have hsecond : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s : ℝ => s ^ 2 • (-(1 / 2 : ℝ) * momentTraceCLM n (B 2 2)))
      (fun s : ℝ => s ^ 2) := by
    apply (herror 2 (by decide)).congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [map_sub, momentTraceCLM_apply (gaussianMomentForm μ 2 s),
      trace_gaussianMomentForm_two μ hm hμ s hs]
    simp only [momentTaylorPolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, map_add, map_smul, map_zero, smul_eq_mul]
    norm_num
    rw [hfirst]
    ring
  have hz := eq_zero_of_isLittleO_pow_smul 2
    (-(1 / 2 : ℝ) * momentTraceCLM n (B 2 2)) hsecond
  rw [← momentTraceCLM_apply]
  linarith

end Preiss
