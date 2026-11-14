module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # Euclidean spaces used by the geometric measure theory library -/

@[expose] public section
namespace Preiss

/-- The standard real Euclidean space of dimension `n`. -/
abbrev Euclidean (n : Nat) := EuclideanSpace Real (Fin n)

end Preiss
