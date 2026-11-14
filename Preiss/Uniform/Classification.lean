import Preiss.Uniform.Transport
import Preiss.Geometry.PlaneMeasure
import FormalizingGMT.MarstrandTheorem

/-! # Classification of uniform measures supported on a plane

Only the full-dimensional classification is used here. No general classification
of uniform measures or analytic support-variety theorem is assumed.
-/

open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- A06a: the unit-ball normalization fixes the scalar uniquely. -/
theorem unitUniform_eq_flat_of_support_subset_plane (hm : 0 < m)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (V : Plane m n) (hsupp : ν.support ⊆ (V.1 : Set (Euclidean n))) :
    ν = unitFlat V := by
  sorry

theorem uniformWithConstant_eq_flat_of_support_subset_plane (hm : 0 < m)
    (ν : Measure (Euclidean n)) {q : ℝ} (hν : IsUniformWithConstant m q ν)
    (V : Plane m n) (hsupp : ν.support ⊆ (V.1 : Set (Euclidean n))) :
    ν = ENNReal.ofReal q • unitFlat V := by
  sorry

end Preiss
