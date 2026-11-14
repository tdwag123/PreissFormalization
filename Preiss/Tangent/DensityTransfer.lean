import Preiss.Tangent.Restriction
import Preiss.Density.Defs
import Preiss.Density.PowerComparison
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

open scoped CompactlySupported

theorem tendsto_integral_blowup_sub_density_mul
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (f : Euclidean n → ℝ) (hf : Measurable f) (hnonneg : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hint : LocallyIntegrable f μ) (x : Euclidean n)
    (hupper : UpperPowerBoundAt m μ x)
    (hdiff : Tendsto (fun r : ℝ ↦
      (∫ y in closedBall x r, ‖f y - f x‖ ∂μ) / (μ (closedBall x r)).toReal)
      (𝓝[>] 0) (𝓝 0))
    (φ : C_c(Euclidean n, ℝ)) :
    Tendsto (fun r : ℝ ↦
      (∫ y, φ y ∂dimensionalBlowup m (μ.withDensity (fun y ↦ ENNReal.ofReal (f y))) x r) -
      f x * (∫ y, φ y ∂dimensionalBlowup m μ x r)) (𝓝[>] 0) (𝓝 0) := by sorry

end Preiss
