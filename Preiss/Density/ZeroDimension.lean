import Preiss.Density.Defs
import Preiss.Rectifiability.Defs

/-! # The zero-dimensional endpoint of Preiss's theorem -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem preiss_zero (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt 0 μ x) : IsRectifiableMeasure 0 μ := by
  sorry

end Preiss
