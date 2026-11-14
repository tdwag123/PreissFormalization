import Preiss.Uniform.TangentNormalization
import Preiss.Uniform.Transport
import Preiss.Tangent.ScalingOrbit
import FormalizingGMT.MarstrandTheorem

/-! # Uniform dimension reduction retaining tangent witnesses

The hyperplane obtained after half-space reduction can have a different normal.
The equality-or-tangent alternative is retained for the scaling-orbit induction.
-/

open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- A02: retain the point, tangent relation, normal and exact unit normalization. -/
theorem exists_halfSpace_dimensionalTangent (hm : 0 < m)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hproper : ν.support ≠ Set.univ) :
    ∃ (y e : Euclidean n) (ξ : Measure (Euclidean n)), y ∈ ν.support ∧ e ≠ 0 ∧
      IsDimensionalTangent m ν ξ y ∧ IsUnitUniform m ξ ∧
      ξ.support ⊆ {z | 0 ≤ inner ℝ z e} := by
  sorry

/-- A03: w need not equal the original half-space normal e. -/
theorem exists_hyperplane_eq_or_dimensionalTangent (hm : 0 < m)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (e : Euclidean n) (he : e ≠ 0)
    (hhalf : ν.support ⊆ {z | 0 ≤ inner ℝ z e}) :
    ∃ (w : Euclidean n) (ξ : Measure (Euclidean n)), w ≠ 0 ∧
      IsUnitUniform m ξ ∧ ξ.support ⊆ {z | inner ℝ z w = 0} ∧
      (ξ = ν ∨ IsDimensionalTangent m ν ξ 0) := by
  sorry

/-- A06b: retain the isometric pushforward's membership in the bounded-radius
support-centered scaling orbit closure. -/
theorem uniform_dimension_reduction (hm : 0 < m) (hmn : m < n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ (L : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n)
      (ξ : Measure (Euclidean (n - 1))), IsUnitUniform m ξ ∧
      IsUniformPseudotangent m ν (ξ.map L) := by
  sorry

end Preiss
