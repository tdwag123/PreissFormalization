module
public import Preiss.Geometry.Euclidean
public import Preiss.Analysis.GradedProjection
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section
open scoped BigOperators
namespace Preiss

abbrev PolynomialFeatureIndex (n N : ℕ) := Σ k : Fin N, (Fin (k.val + 1) → Fin n)
abbrev PolynomialFeatureSpace (n N : ℕ) := EuclideanSpace ℝ (PolynomialFeatureIndex n N)

noncomputable def polynomialFeature {n : ℕ} (N : ℕ) (x : Euclidean n) :
    PolynomialFeatureSpace n N :=
  WithLp.toLp 2 (fun i =>
    Real.sqrt ((2 : ℝ) ^ (i.1.val + 1) / ((i.1.val + 1).factorial : ℝ)) *
      ∏ j, x (i.2 j))

noncomputable def polynomialFeatureBlock {n N : ℕ} (k : Fin N) :
    Submodule ℝ (PolynomialFeatureSpace n N) :=
  Submodule.span ℝ (Set.range (fun ι : Fin (k.val + 1) → Fin n =>
    EuclideanSpace.single (⟨k, ι⟩ : PolynomialFeatureIndex n N) (1 : ℝ)))

noncomputable def polynomialFeatureProjection {n N : ℕ} (k : Fin N) :
    PolynomialFeatureSpace n N →L[ℝ] PolynomialFeatureSpace n N :=
  (polynomialFeatureBlock (n := n) k).starProjection

theorem polynomialFeature_inner {n N : ℕ} (x y : Euclidean n) :
    inner ℝ (polynomialFeature N x) (polynomialFeature N y) =
      ∑ k : Fin N, ((2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)) *
        (inner ℝ x y) ^ (k.val + 1) := by
  sorry

theorem polynomialFeatureProjection_isOrthogonalGrading (n N : ℕ) :
    IsOrthogonalGrading (polynomialFeatureProjection (n := n) (N := N)) := by
  sorry

theorem polynomialFeatureProjection_inner {n N : ℕ} (k : Fin N)
    (x y : Euclidean n) :
    inner ℝ (polynomialFeatureProjection k (polynomialFeature N x))
      (polynomialFeature N y) =
      ((2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)) *
        (inner ℝ x y) ^ (k.val + 1) := by
  sorry

theorem exists_normPolynomial_feature_functionals (n q : ℕ) :
    ∃ L : Fin q → PolynomialFeatureSpace n (2 * q) →L[ℝ] ℝ,
      ∀ j x, L j (polynomialFeature (2 * q) x) = ‖x‖ ^ (2 * (j.val + 1)) := by
  sorry

end Preiss
