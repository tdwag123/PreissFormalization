module
public import Preiss.Analysis.PolynomialFeatures
public import Preiss.Analysis.LinearMapIntegral
public import Preiss.Uniform.MomentForms
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

theorem featureMoment_apply_feature (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (N : ℕ)
    (s : ℝ) (hs : 0 < s) (x : Euclidean n) :
    featureMoment μ N s (polynomialFeature N x) =
      ∑ k ∈ Finset.range N, gaussianMomentForm μ (k + 1) s (fun _ => x) := by
  sorry

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
