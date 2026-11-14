module
public import Preiss.Geometry.Projections

/-! # Homogeneity of distance to a linear plane -/
@[expose] public section
open MeasureTheory Metric Set
namespace Preiss
variable {m n : ℕ}

theorem infDist_smul_plane (V : Plane m n) (z : Euclidean n) (c : ℝ) :
    infDist (c • z) (V.1 : Set (Euclidean n)) =
      ‖c‖ * infDist z (V.1 : Set (Euclidean n)) := by
  rw [infDist_submodule_eq_norm_sub_starProjection,
    infDist_submodule_eq_norm_sub_starProjection, map_smul, ← smul_sub, norm_smul]

end Preiss
