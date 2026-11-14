module

public import Preiss.Rectifiability.Basic
public import Preiss.Geometry.Projections
public import Preiss.Geometry.PlaneMeasure
public import Preiss.Rectifiability.GraphDefs

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def graphMap (V : Plane m n) (f : V.1 → ↥(V.1ᗮ)) (v : V.1) : Euclidean n :=
  (v : Euclidean n) + (f v : Euclidean n)

theorem graphMap_lipschitz_antilipschitz (V : Plane m n)
    (f : V.1 → ↥(V.1ᗮ)) {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (1 + K) (graphMap V f) ∧
      AntilipschitzWith 1 (graphMap V f) ∧
      ∀ v, proj V (graphMap V f v) = (v : Euclidean n) := by sorry

theorem isClosed_and_measure_closedBall_lt_top {s : Set (Euclidean n)}
    (hs : IsLipschitzGraph m s) :
    IsClosed s ∧ ∀ x r, (Measure.hausdorffMeasure (m : ℝ)) (s ∩ closedBall x r) < ∞ := by sorry

theorem countablyRectifiable_subset_graph {s t : Set (Euclidean n)}
    (hs : IsLipschitzGraph m s) (ht : t ⊆ s) : CountablyRectifiable m t := by sorry

end Preiss
