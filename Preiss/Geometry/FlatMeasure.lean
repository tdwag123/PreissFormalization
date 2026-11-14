module

public import Preiss.Geometry.Planes
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Flat measures -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace Preiss
variable {n : Nat}

/-- Flat measures form a cone: all positive finite multiples are included. -/
def IsFlat (m : ℕ) (ν : Measure (Euclidean n)) : Prop :=
  ∃ V : Plane m n, ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧
    ν = c • (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n))

end Preiss
