module

public import Preiss.Rectifiability.Defs

/-! # Rectifiability of the zero measure -/

@[expose] public section
open MeasureTheory
namespace Preiss
variable {m : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The empty carrier witnesses rectifiability of the zero measure. -/
theorem zero_isRectifiableMeasure : IsRectifiableMeasure m (0 : Measure X) := by
  sorry

end Preiss
