module

public import Preiss.Geometry.Euclidean
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Linear planes of prescribed dimension -/

@[expose] public section

namespace Preiss

/-- An m-dimensional linear plane through the origin. Topology on planes is separate. -/
abbrev Plane (m n : ℕ) := {V : Submodule ℝ (Euclidean n) // Module.finrank ℝ V = m}

end Preiss
