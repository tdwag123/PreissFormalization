module

public import Preiss.Geometry.Projections
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def cylinder (V : Plane m n) (p : Euclidean n) (r : ℝ) : Set (Euclidean n) :=
  {y | dist (proj V y) p < r}

theorem exists_unit_small_projection_of_avoids_cylinder (hm : 0 < m)
    (V W : Plane m n) (z p : Euclidean n) {ρ r : ℝ}
    (hp : p ∈ V.1) (hρ : 0 < ρ) (hr : 0 < r)
    (hd : dist (proj V z) p = ρ)
    (havoid : ∀ y : Euclidean n, y - z ∈ W.1 → y ∈ ball z r →
      y ∉ cylinder V p (ρ / 4)) :
    ∃ w : Euclidean n, w ∈ W.1 ∧ ‖w‖ = 1 ∧ ‖proj V w‖ ≤ 4 * ρ / r := by sorry

end Preiss
