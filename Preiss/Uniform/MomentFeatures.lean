module
public import Preiss.Analysis.PolynomialFeatures
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

theorem featureMoment_vanishes_weightedComplement
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (N : ℕ) (s : ℝ) (hs : 0 < s) (u : PolynomialFeatureSpace n N)
    (hu : u ∈ weightedComplement polynomialFeatureProjection (supportFeatureSpan μ N) s) :
    featureMoment μ N s u = 0 := by
  sorry

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
