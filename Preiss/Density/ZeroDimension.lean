import Preiss.Density.Defs
import Preiss.Density.Atoms
import Preiss.Rectifiability.Countable
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! # The zero-dimensional endpoint of Preiss's theorem -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem preiss_zero (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt 0 μ x) : IsRectifiableMeasure 0 μ := by
  have hc : Set.Countable {x : Euclidean n | 0 < μ {x}} := by
    exact Measure.countable_meas_pos_of_disjoint_iUnion
      (fun x => measurableSet_singleton x) (fun x y hxy => disjoint_singleton.mpr hxy)
  refine ⟨by simpa using absolutelyContinuous_hausdorffMeasure_zero μ,
    {x | 0 < μ {x}}, countablyRectifiable_of_countable 0 hc, ?_⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [h] with x hx
  have hxatom : 0 < μ {x} := by
    simpa only [Nat.cast_zero, lowerDensity_zero_eq_singleton] using hx.1
  exact fun hxnot => hxnot hxatom

end Preiss
