module
public import Preiss.Geometry.PlaneMeasure
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Maps.Proper.Basic

/-! # Regularity and positive ball mass of flat measures -/
@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem regular_flatOn (V : Plane m n) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    (flatOn V c).Regular := by
  let μV : Measure V.1 := Measure.hausdorffMeasure (m : ℝ)
  haveI : Measure.IsAddHaarMeasure μV := by
    dsimp [μV]
    simpa only [V.property] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ V.1 : ℝ) : Measure V.1))
  haveI : IsFiniteMeasureOnCompacts (μV.map (fun v : V.1 => (v : Euclidean n))) := by
    constructor
    intro K hK
    rw [Measure.map_apply continuous_subtype_val.measurable hK.measurableSet]
    exact (V.1.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hK).measure_lt_top
  haveI : IsFiniteMeasureOnCompacts
      ((Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n))) := by
    rw [← map_hausdorffMeasure_subtype_eq_restrict V]
    exact inferInstanceAs (IsFiniteMeasureOnCompacts
      (μV.map (fun v : V.1 => (v : Euclidean n))))
  haveI : IsFiniteMeasureOnCompacts (flatOn V c) :=
    IsFiniteMeasureOnCompacts.smul _ hc
  infer_instance

theorem flatOn_ball_pos (V : Plane m n) {c : ℝ≥0∞} (hc : 0 < c)
    {z : Euclidean n} (hz : z ∈ V.1) {r : ℝ} (hr : 0 < r) :
    0 < flatOn V c (ball z r) := by
  let μV : Measure V.1 := Measure.hausdorffMeasure (m : ℝ)
  haveI : Measure.IsAddHaarMeasure μV := by
    dsimp [μV]
    simpa only [V.property] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ V.1 : ℝ) : Measure V.1))
  have hball : (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n))
      (ball z r) = μV (ball (⟨z, hz⟩ : V.1) r) := by
    rw [← map_hausdorffMeasure_subtype_eq_restrict V,
      Measure.map_apply continuous_subtype_val.measurable measurableSet_ball]
    rfl
  rw [flatOn, Measure.smul_apply, smul_eq_mul, hball]
  exact ENNReal.mul_pos hc.ne' (measure_ball_pos μV _ hr).ne'

end Preiss
