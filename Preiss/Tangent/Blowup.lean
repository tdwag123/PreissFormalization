module

public import Preiss.Geometry.Euclidean
public import Mathlib.MeasureTheory.Measure.Map

/-! # Dimensionally normalized blow-ups

The affine map is definitionally equal to FormalizingGMT's `blowUpMap`.
The density-dependent correspondence with its arbitrary scalar tangents is separate.
-/

@[expose] public section
open MeasureTheory
namespace Preiss
variable {n : Nat}

/-- Fixed dimensional normalization, as in De Lellis. This is NOT the
arbitrary scalar sequence in FormalizingGMT's `IsTangentMeasure`. -/
noncomputable def dimensionalBlowup (m : ℕ) (μ : Measure (Euclidean n))
    (x : Euclidean n) (r : ℝ) : Measure (Euclidean n) :=
  (ENNReal.ofReal (r ^ m))⁻¹ • μ.map (fun y => r⁻¹ • (y - x))

end Preiss
