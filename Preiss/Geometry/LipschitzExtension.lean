module

public import Preiss.Geometry.Euclidean
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_lipschitz_extension_euclidean (A : Set (Euclidean m))
    (f : A → Euclidean n) {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ F : Euclidean m → Euclidean n, (∃ L : ℝ≥0, LipschitzWith L F) ∧
      ∀ x : A, F x = f x := by sorry

end Preiss
