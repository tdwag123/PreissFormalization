module
public import Preiss.Analysis.GaussianGrowth
public import Preiss.Analysis.PolynomialFeatures
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Gaussian integrability of finite polynomial feature vectors

A polynomial ball-growth bound suffices. Neither regularity nor uniformity is needed.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Preiss

theorem integrable_gaussian_polynomialFeature {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (N : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • polynomialFeature N z) μ := by
  apply integrable_piLp_iff.mpr
  intro i
  let P : MvPolynomial (Fin n) ℝ := ∏ a : Fin (i.1.val+1), MvPolynomial.X (i.2 a)
  have hP (z : Euclidean n) : MvPolynomial.eval (fun j => z j) P = ∏ a, z (i.2 a) := by
    simp [P]
  have hint : Integrable (fun z : Euclidean n => (∏ a, z (i.2 a)) *
      Real.exp (-s * ‖z‖ ^ 2)) μ := by
    simpa only [pow_zero, one_mul, hP] using
      integrable_norm_pow_mul_polynomial_mul_gaussian μ C p hgrowth.1 hgrowth.2.2 P 0 s hs
  change Integrable (fun z : Euclidean n => Real.exp (-s * ‖z‖ ^ 2) *
    (Real.sqrt ((2 : ℝ) ^ (i.1.val+1) / ((i.1.val+1).factorial : ℝ)) *
      ∏ a, z (i.2 a))) μ
  convert hint.const_mul (Real.sqrt ((2 : ℝ) ^ (i.1.val+1) / ((i.1.val+1).factorial : ℝ))) using 1
  funext z
  ring

theorem integrable_featureMomentKernel_of_growth {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (N : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) •
      (innerSL ℝ (polynomialFeature N z)).comp
        (weightedGrading polynomialFeatureProjection s)) μ := by
  let A := weightedGrading (polynomialFeatureProjection (n := n) (N := N)) s
  let T : (PolynomialFeatureSpace n N →L[ℝ] ℝ) →L[ℝ]
      (PolynomialFeatureSpace n N →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (PolynomialFeatureSpace n N) (PolynomialFeatureSpace n N) ℝ).flip A
  have h := T.integrable_comp ((innerSL ℝ).integrable_comp
    (integrable_gaussian_polynomialFeature μ C p hgrowth N s hs))
  convert h using 1
  funext z
  ext u
  simp [T, A, inner_smul_left]

end Preiss
