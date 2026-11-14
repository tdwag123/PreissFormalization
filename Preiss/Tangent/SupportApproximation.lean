import Preiss.Tangent.Defs
import Preiss.Density.Defs
import Preiss.Analysis.MeasureHull
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.HausdorffDistance

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal
namespace Preiss
variable {n m : ℕ}

/-- Relative measure-density one, expressed without division by a possibly zero ball mass. -/
def IsMeasureDensityOnePoint (μ : Measure (Euclidean n)) (H : Set (Euclidean n))
    (a : Euclidean n) : Prop :=
  ∀ γ : ℝ≥0∞, 0 < γ → ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
    μ (closedBall a ρ \ H) ≤ γ * μ (closedBall a ρ)

/-- The set `D` need not be measurable. Density one is imposed on its measurable hull. -/
theorem dist_badSet_rescaled_tendsto_zero
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (D : Set (Euclidean n)) (hD : μ D ≠ ∞) (a : Euclidean n) (ha : a ∈ D)
    (hdens : IsMeasureDensityOnePoint μ (toMeasurable μ D) a)
    (hupper : dimensional_upper_density μ.toOuterMeasure (m : ℝ) a < ∞)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    (hlim : Measure.WeaklyConverges (fun i => dimensionalBlowup m μ a (r i)) ν)
    (y : Euclidean n) (hy : y ∈ ν.support) :
    Tendsto (fun i => infDist (a + r i • y) D / r i) atTop (𝓝 0) := by
  sorry

/-- Approximate nearest points suffice; the arbitrary set `D` need not be closed. -/
theorem exists_badSet_points_rescaled_tendsto
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (D : Set (Euclidean n)) (hD : μ D ≠ ∞) (a : Euclidean n) (ha : a ∈ D)
    (hdens : IsMeasureDensityOnePoint μ (toMeasurable μ D) a)
    (hupper : dimensional_upper_density μ.toOuterMeasure (m : ℝ) a < ∞)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    (hlim : Measure.WeaklyConverges (fun i => dimensionalBlowup m μ a (r i)) ν)
    (y : Euclidean n) (hy : y ∈ ν.support) :
    ∃ a' : ℕ → Euclidean n, (∀ i, a' i ∈ D) ∧
      Tendsto (fun i => (r i)⁻¹ • (a' i - a)) atTop (𝓝 y) := by
  sorry

end Preiss
