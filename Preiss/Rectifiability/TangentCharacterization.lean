import Preiss.Rectifiability.TangentNecessity
import Preiss.Rectifiability.MarstrandMattila.MeasureCriterion

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem rectifiable_iff_density_bounds_and_flat_tangents
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] :
    IsRectifiableMeasure m μ ↔
      (∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x) ∧
      (∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) := by sorry

end Preiss
