module
public import Preiss.Analysis.PolynomialFeatures
public import Preiss.Analysis.AnalyticProjectionApproximation
public import Preiss.Analysis.FiniteDimensionalBigO
public import Preiss.Analysis.LinearMapIntegral
public import Preiss.Uniform.MomentForms
public import Preiss.Uniform.MomentEstimates
public import Preiss.Analysis.GaussianFeatures
public import Preiss.Uniform.Defs
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Preiss
variable {n m q : ℕ}

noncomputable def supportFeatureSpan (μ : Measure (Euclidean n)) (N : ℕ) :
    Submodule ℝ (PolynomialFeatureSpace n N) :=
  Submodule.span ℝ (polynomialFeature N '' μ.support)

noncomputable def featureMoment (μ : Measure (Euclidean n)) (N : ℕ) (s : ℝ) :
    PolynomialFeatureSpace n N →L[ℝ] ℝ :=
  (gaussianMass μ s)⁻¹ • ∫ z,
    Real.exp (-s * ‖z‖ ^ 2) •
      (innerSL ℝ (polynomialFeature N z)).comp
        (weightedGrading polynomialFeatureProjection s) ∂μ

theorem featureMoment_apply_feature_of_growth {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (N : ℕ) (s : ℝ) (hs : 0 < s) (x : Euclidean n) :
    featureMoment μ N s (polynomialFeature N x) =
      ∑ k ∈ Finset.range N, gaussianMomentForm μ (k + 1) s (fun _ => x) := by
  have hK (k : ℕ) : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z) μ :=
    integrable_gaussianMomentKernel_of_integrable_norm μ k s
      (integrable_norm_pow_mul_gaussian_of_ball_bound μ C p hgrowth.1 hgrowth.2.2 k s hs)
  have hI (k : Fin N) : Integrable (fun z => (inner ℝ z x) ^ (k.val+1) *
      Real.exp (-s * ‖z‖ ^ 2)) μ := by
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k.val+1) => Euclidean n) ℝ
      (fun _ => x)).integrable_comp (hK (k.val+1))
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply,
      momentKernel_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_comm] using h
  have hJ (k : Fin N) : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) *
      ((s ^ (k.val+1) * ((2 : ℝ) ^ (k.val+1) / ((k.val+1).factorial : ℝ))) *
        (inner ℝ z x) ^ (k.val+1))) μ := by
    convert (hI k).const_mul (s ^ (k.val+1) *
      ((2 : ℝ) ^ (k.val+1) / ((k.val+1).factorial : ℝ))) using 1
    funext z
    ring
  rw [featureMoment, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.integral_apply (integrable_featureMomentKernel_of_growth μ C p hgrowth N s hs)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  simp_rw [polynomialFeature_weighted_inner, Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _ => hJ k), Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [gaussianMomentForm_apply μ (k.val+1) s (hK (k.val+1))]
  have heq : (∫ z, Real.exp (-s * ‖z‖ ^ 2) *
      ((s ^ (k.val+1) * ((2 : ℝ) ^ (k.val+1) / ((k.val+1).factorial : ℝ))) *
        (inner ℝ z x) ^ (k.val+1)) ∂μ) =
      (s ^ (k.val+1) * ((2 : ℝ) ^ (k.val+1) / ((k.val+1).factorial : ℝ))) *
        ∫ z, (inner ℝ z x) ^ (k.val+1) * Real.exp (-s * ‖z‖ ^ 2) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [heq]
  simp only [gaussianMoment, gaussianMass, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_pow]
  ring
theorem featureMoment_apply_feature (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (N : ℕ)
    (s : ℝ) (hs : 0 < s) (x : Euclidean n) :
    featureMoment μ N s (polynomialFeature N x) =
      ∑ k ∈ Finset.range N, gaussianMomentForm μ (k + 1) s (fun _ => x) := by
  exact featureMoment_apply_feature_of_growth μ 1 (m : ℝ)
    (IsUnitUniform.hasPolynomialGrowthBound μ hμ) N s hs x

theorem featureMoment_eq_zero_of_mem_weightedComplement {n : ℕ}
    (μ : Measure (Euclidean n)) (N : ℕ) (s : ℝ)
    (u : PolynomialFeatureSpace n N)
    (hu : u ∈ weightedComplement polynomialFeatureProjection (supportFeatureSpan μ N) s) :
    featureMoment μ N s u = 0 := by
  let F := fun z : Euclidean n => Real.exp (-s * ‖z‖ ^ 2) •
    (innerSL ℝ (polynomialFeature N z)).comp (weightedGrading polynomialFeatureProjection s)
  have hz : (∫ z, F z ∂μ) u = 0 := by
    apply integral_apply_eq_zero_of_ae
    filter_upwards [μ.support_mem_ae] with z hz
    have hmem : polynomialFeature N z ∈ supportFeatureSpan μ N :=
      Submodule.subset_span ⟨z,hz,rfl⟩
    have horth : weightedGrading polynomialFeatureProjection s u ∈
        (supportFeatureSpan μ N)ᗮ := hu
    have hinner := Submodule.inner_right_of_mem_orthogonal hmem horth
    simp only [F, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, hinner, smul_zero]
  change ((gaussianMass μ s)⁻¹ • ∫ z, F z ∂μ) u = 0
  rw [ContinuousLinearMap.smul_apply, hz, smul_zero]

theorem featureMoment_vanishes_weightedComplement
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (N : ℕ) (s : ℝ) (hs : 0 < s) (u : PolynomialFeatureSpace n N)
    (hu : u ∈ weightedComplement polynomialFeatureProjection (supportFeatureSpan μ N) s) :
    featureMoment μ N s u = 0 := by
  exact featureMoment_eq_zero_of_mem_weightedComplement μ N s u hu

theorem featureMoment_operator_remainder
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (q : ℕ) (hq : 0 < q)
    (L : Fin q → PolynomialFeatureSpace n (2*q) →L[ℝ] ℝ)
    (hL : ∀ j x, L j (polynomialFeature (2*q) x) = ‖x‖^(2*(j.val+1))) :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun s : ℝ => (featureMoment μ (2*q) s -
        ∑ j : Fin q,(s^(j.val+1)/((j.val+1).factorial : ℝ)) • L j).comp
          (supportFeatureSpan μ (2*q)).subtypeL)
      (fun s : ℝ => s^((q : ℝ)+1/2)) := by
  let T (s : ℝ) : PolynomialFeatureSpace n (2*q) →L[ℝ] ℝ :=
    featureMoment μ (2*q) s - ∑ j : Fin q,(s^(j.val+1)/((j.val+1).factorial : ℝ)) • L j
  change Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
    (fun s => (T s).comp (Submodule.span ℝ (polynomialFeature (2*q) '' μ.support)).subtypeL)
    (fun s : ℝ => s^((q : ℝ)+1/2))
  apply isBigO_restrict_span_of_forall_mem
  rintro v ⟨x,hx,rfl⟩
  obtain ⟨C,hC,hbound⟩ := gaussianMoment_taylor_remainder (n := n) hm q hq
  apply Asymptotics.IsBigO.of_bound (C*(‖x‖^2)^((q : ℝ)+1/2))
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpoly : (∑ j : Fin q,(s^(j.val+1)/((j.val+1).factorial : ℝ))*‖x‖^(2*(j.val+1))) =
      ∑ j ∈ Finset.range q,s^(j+1)*‖x‖^(2*(j+1))/((j+1).factorial : ℝ) := by
    calc
      _ = ∑ j : Fin q,s^(j.val+1)*‖x‖^(2*(j.val+1))/((j.val+1).factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun j : ℕ => s^(j+1)*‖x‖^(2*(j+1))/((j+1).factorial : ℝ)) q
  have heval : T s (polynomialFeature (2*q) x) =
      (∑ k ∈ Finset.range (2*q),gaussianMomentForm μ (k+1) s (fun _ => x)) -
        ∑ j ∈ Finset.range q,s^(j+1)*‖x‖^(2*(j+1))/((j+1).factorial : ℝ) := by
    simp only [T,ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul,hL]
    rw [hpoly,featureMoment_apply_feature μ hm hμ (2*q) s hs]
  rw [heval]
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hs.le _)]
  have H := hbound μ hμ x hx s hs
  rw [Real.mul_rpow hs.le (sq_nonneg ‖x‖)] at H
  exact H.trans_eq (by ring)


theorem exists_featureMoment_analytic_approximation
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (q : ℕ) (hq : 0 < q) :
    ∃ a : ℝ → PolynomialFeatureSpace n (2*q) →L[ℝ] ℝ,
      AnalyticAt ℝ a 0 ∧ a 0 = 0 ∧
      Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
        (fun s => featureMoment μ (2*q) s - a s)
        (fun s : ℝ => s^((q : ℝ)+1/2)) := by
  obtain ⟨L,hL⟩ := exists_normPolynomial_feature_functionals n q
  let g : ℝ → PolynomialFeatureSpace n (2*q) →L[ℝ] ℝ :=
    fun s => ∑ j : Fin q,(s^(j.val+1)/((j.val+1).factorial : ℝ)) • L j
  have hg : AnalyticAt ℝ g 0 := by
    have hj (j : Fin q) : AnalyticAt ℝ
        (fun s : ℝ => (s^(j.val+1)/((j.val+1).factorial : ℝ)) • L j) 0 :=
      ((analyticAt_id.pow _).div_const).smul analyticAt_const
    have h := Finset.analyticAt_sum Finset.univ (fun j _ => hj j)
    convert h using 1
    ext s
    simp only [g,Finset.sum_apply]
  have hg0 : g 0 = 0 := by simp [g]
  exact exists_analyticApproximation_of_weightedComplement
    polynomialFeatureProjection (polynomialFeatureProjection_isOrthogonalGrading n (2*q))
    (supportFeatureSpan μ (2*q)) (featureMoment μ (2*q)) g hg hg0
    (fun s : ℝ => s^((q : ℝ)+1/2))
    (fun s _ w hw => featureMoment_eq_zero_of_mem_weightedComplement μ (2*q) s w hw)
    (featureMoment_operator_remainder μ hm hμ q hq L hL)


variable {N : ℕ}
theorem featureMoment_comp_multilinearBlock_of_growth
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (k : Fin N) (s : ℝ) (hs : 0 < s) :
    (featureMoment μ N s).compContinuousMultilinearMap (polynomialFeatureMultilinearBlock k) =
      gaussianMomentForm μ (k.val+1) s := by
  have hK : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel (k.val+1) z) μ :=
    integrable_gaussianMomentKernel_of_integrable_norm μ (k.val+1) s
      (integrable_norm_pow_mul_gaussian_of_ball_bound μ C p hgrowth.1 hgrowth.2.2
        (k.val+1) s hs)
  ext u
  change featureMoment μ N s (polynomialFeatureMultilinearBlock k u) =
    gaussianMomentForm μ (k.val+1) s u
  rw [featureMoment,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.integral_apply (integrable_featureMomentKernel_of_growth μ C p hgrowth N s hs),
    gaussianMomentForm,ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.integral_apply hK]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,weightedGrading_polynomialFeatureMultilinearBlock,
    inner_smul_right,inner_polynomialFeature_multilinearBlock,
    ContinuousMultilinearMap.smul_apply,momentKernel_apply,smul_eq_mul]
  have hi : (∫ z, Real.exp (-s * ‖z‖^2) *
      (s^(k.val+1) * (((2 : ℝ)^(k.val+1)/((k.val+1).factorial : ℝ)) *
        ∏ j,inner ℝ z (u j))) ∂μ) =
      (s^(k.val+1) * ((2 : ℝ)^(k.val+1)/((k.val+1).factorial : ℝ))) *
        ∫ z,Real.exp (-s * ‖z‖^2) * ∏ j,inner ℝ z (u j) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [hi,mul_pow]
  ring

theorem polynomialFeatureMomentRecovery_featureMoment_of_growth
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (k : Fin N) (s : ℝ) (hs : 0 < s) :
    polynomialFeatureMomentRecovery k (featureMoment μ N s) =
      gaussianMomentForm μ (k.val+1) s := by
  change (featureMoment μ N s).compContinuousMultilinearMap
    (symmetrizeContinuousMultilinearMap (polynomialFeatureMultilinearBlock k)) = _
  rw [comp_symmetrizeContinuousMultilinearMap,
    featureMoment_comp_multilinearBlock_of_growth μ C p hgrowth k s hs]
  exact symmetrizeContinuousMultilinearMap_eq_self _
    (gaussianMomentForm_permute μ (k.val+1) s)

end Preiss
