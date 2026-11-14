import Preiss.Tangent.Defs
import Preiss.Density.Defs
import FormalizingGMT.TangentMeasures.Basic

/-! # Arbitrary scalar and dimensional tangents

The theorem bodies are explicit proof obligations.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem tangent_iff_dimensional_ray (μ ν : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (h : HasPositiveFiniteDensityAt m μ x) :
    IsTangentMeasure μ ν x ↔ ∃ ξ : Measure (Euclidean n),
      IsDimensionalTangent m μ ξ x ∧
        ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ ν = c • ξ := by
  sorry


end Preiss
