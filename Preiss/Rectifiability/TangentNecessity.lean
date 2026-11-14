import Preiss.Rectifiability.GraphCover
import Preiss.Rectifiability.DensityRepresentation
import Preiss.Rectifiability.GraphBlowup
import Preiss.Tangent.DensityTransfer
import Preiss.Tangent.Normalization
import Preiss.Geometry.FlatMeasure
import Preiss.Geometry.PlaneMeasure

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem rectifiable_has_flat_blowup_limit
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (hrect : IsRectifiableMeasure m μ) :
    ∀ᵐ x ∂μ, ∃ (V : Plane m n) (c : ℝ≥0∞), 0 < c ∧ c < ∞ ∧
      ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
        Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m μ x (r i)) (flatOn V c) := by
  sorry

theorem rectifiable_has_density_and_tangent_plane
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (hrect : IsRectifiableMeasure m μ) :
    ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x ∧ ∃ V : Plane m n,
      ∀ ν : Measure (Euclidean n), IsTangentMeasure μ ν x ↔
        ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ ν = flatOn V c := by sorry

end Preiss
