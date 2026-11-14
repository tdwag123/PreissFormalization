import Preiss.Uniform.DimensionReduction
import Preiss.Uniform.Classification

/-! # Flat pseudotangents of uniform measures

The radii remain at most one, as required by the support-centered recentering argument.
-/

open MeasureTheory Metric Set Filter Topology
namespace Preiss
variable {m n : ℕ}

/-- A06c: a genuinely flat normalized limit, with all sequence witnesses retained. -/
theorem uniform_has_flat_pseudotangent (hm : 0 < m) (hmn : m ≤ n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ (V : Plane m n) (a : ℕ → Euclidean n) (r : ℕ → ℝ),
      (∀ i, a i ∈ ν.support) ∧ (∀ i, 0 < r i ∧ r i ≤ 1) ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m ν (a i) (r i)) (unitFlat V) := by
  sorry

end Preiss
