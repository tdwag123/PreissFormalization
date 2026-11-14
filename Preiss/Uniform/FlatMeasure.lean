module

public import Preiss.Geometry.UnitFlat
public import Preiss.Uniform.Defs

/-! # Normalized plane measures are unit uniform -/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem isUnitUniform_unitFlat (V : Plane m n) : IsUnitUniform m (unitFlat V) := by
  refine ⟨regular_unitFlat V, ?_, ?_⟩
  · rw [unitFlat_support]
    exact V.1.zero_mem
  · intro x hx r hr
    rw [unitFlat_support] at hx
    exact unitFlat_closedBall V x hx hr

end Preiss
