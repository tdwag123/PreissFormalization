module

public import Preiss.Geometry.Projections
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def closedTube (x : Euclidean n) (V : Plane m n) (r : ℝ) : Set (Euclidean n) :=
  {y | infDist (y - x) (V.1 : Set (Euclidean n)) ≤ r}

def cone (x : Euclidean n) (V : Plane m n) (a : ℝ) : Set (Euclidean n) :=
  {y | ‖(y - x) - proj V (y - x)‖ ≤ a * ‖proj V (y - x)‖}

end Preiss
