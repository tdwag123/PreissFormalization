import Preiss.Tangent.Compactness
import Preiss.Geometry.FlatMeasure
import Preiss.Rectifiability.WeakApproximation.Defs
import Preiss.Geometry.PlaneMeasure
import Preiss.Geometry.Cones

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem tendsto_mass_outside_tube_of_flat_limit
    (ν : ℕ → Measure (Euclidean n)) (hν : ∀ i, (ν i).Regular)
    (V : Plane m n) {c : ℝ≥0∞} (hc : 0 < c) (hcfin : c < ∞)
    (hlim : Measure.WeaklyConverges ν (flatOn V c)) {η R : ℝ}
    (hη : 0 < η) (hR : 0 < R) :
    Tendsto (fun i ↦ ν i (closedBall 0 R ∩
      {z | η ≤ infDist z (V.1 : Set (Euclidean n))})) atTop (𝓝 0) := by sorry

theorem eventually_ball_mass_lower_bound_of_flat_limit
    (ν : ℕ → Measure (Euclidean n)) (hν : ∀ i, (ν i).Regular)
    (V : Plane m n) {c : ℝ≥0∞} (hc : 0 < c) (hcfin : c < ∞)
    (hlim : Measure.WeaklyConverges ν (flatOn V c)) {η R : ℝ}
    (hη : 0 < η) (hR : 0 < R) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ i in atTop, ∀ z : Euclidean n,
      z ∈ V.1 → z ∈ closedBall 0 R → ENNReal.ofReal a ≤ ν i (ball z η) := by sorry

theorem weaklyLinearlyApproximableAt_of_all_tangents_flat
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensitiesAt m μ x)
    (ht : ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) :
    MeasureWeaklyLinearlyApproximableAt m μ x := by sorry

end Preiss
