module

public import Preiss.Geometry.Projections
public import Preiss.Geometry.PlaneMeasure
public import Preiss.Geometry.Cones
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem hausdorffMeasure_projected_tube_le (m n : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V W : Plane m n) (a w : Euclidean n)
      (R η ε : ℝ), 0 < R → 0 ≤ η → 0 ≤ ε → w ∈ W.1 → ‖w‖ = 1 →
      ‖proj V w‖ ≤ ε →
      (Measure.hausdorffMeasure (m : ℝ)) (proj V '' (closedTube a W (η * R) ∩ closedBall a R)) ≤
        ENNReal.ofReal (C * (ε + η) * R ^ m) := by sorry

end Preiss
