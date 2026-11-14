import Preiss.Density.Defs
import Preiss.Density.PowerComparison

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem absolutelyContinuous_hausdorff_of_upper_density_finite
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, dimensional_upper_density μ.toOuterMeasure (m : ℝ) x < ∞) :
    μ ≪ (Measure.hausdorffMeasure (m : ℝ)) := by sorry

end Preiss
