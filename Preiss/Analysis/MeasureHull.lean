module
public import Mathlib.MeasureTheory.Measure.Basic

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace Preiss

theorem measure_toMeasurable_inter_eq_zero_of_disjoint {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (D U : Set α)
    (hD : μ D ≠ ∞) (hU : MeasurableSet U) (hdisj : Disjoint D U) :
    μ (toMeasurable μ D ∩ U) = 0 := by
  rw [μ.measure_toMeasurable_inter hU hD, hdisj.inter_eq, measure_empty]

end Preiss
