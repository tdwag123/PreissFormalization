import Preiss.Density.Defs
import Preiss.Rectifiability.Defs

/-! # Zero and excessive dimensions

The theorem bodies are explicit proof obligations.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem preiss_zero (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt 0 μ x) : IsRectifiableMeasure 0 μ := by
  sorry

theorem measure_zero_of_dimension_gt (hmn : n < m)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) : μ = 0 := by
  sorry


end Preiss
