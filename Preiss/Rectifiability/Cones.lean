module

public import Preiss.Geometry.Cones
public import Preiss.Geometry.LipschitzExtension
public import Preiss.Rectifiability.Graphs

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_lipschitzGraph_of_pairwise_mem_cone
    (V : Plane m n) (F : Set (Euclidean n)) {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ x ∈ F, ∀ y ∈ F, y ∈ cone x V a) :
    ∃ f : V.1 → ↥(V.1ᗮ), (∃ K : ℝ≥0, LipschitzWith K f) ∧
      F ⊆ Set.range (graphMap V f) := by sorry

end Preiss
