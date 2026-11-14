module

public import Preiss.Geometry.Planes
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-! # Lipschitz graphs over linear planes -/

@[expose] public section
open scoped NNReal

namespace Preiss

/-- A full Lipschitz graph over an m-plane, with values in its orthogonal complement.
Affine translates are included: the graphing function need not vanish at zero.
Containment in countably many such graphs is a separate covering condition. -/
def IsLipschitzGraph {n : ℕ} (m : ℕ) (s : Set (Euclidean n)) : Prop :=
  ∃ (V : Plane m n) (f : V.1 → ↥(V.1ᗮ)),
    (∃ K : ℝ≥0, LipschitzWith K f) ∧
      s = Set.range (fun v : V.1 => (v : Euclidean n) + (f v : Euclidean n))

end Preiss
