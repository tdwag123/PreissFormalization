module
public import Preiss.Analysis.PolynomialFeatures
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
    (L : Fin q → PolynomialFeatureSpace n (2 * q) →L[ℝ] ℝ)
    (hL : ∀ j x, L j (polynomialFeature (2 * q) x) = ‖x‖ ^ (2 * (j.val + 1))) :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun s : ℝ => (featureMoment μ (2 * q) s -
        ∑ j : Fin q, (s ^ (j.val + 1) / ((j.val + 1).factorial : ℝ)) • L j).comp
          (supportFeatureSpan μ (2 * q)).subtypeL)
      (fun s : ℝ => s ^ ((q : ℝ) + 1 / 2)) := by
  sorry

end Preiss
