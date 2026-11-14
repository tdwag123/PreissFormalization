module

public import Preiss.Geometry.PlaneRegularity
public import Preiss.Geometry.FlatMeasure
public import Preiss.Analysis.MeasureSupport

/-! # Basic properties of normalized plane measures -/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem flatOn_support (V : Plane m n) {c : ℝ≥0∞} (hc : 0 < c) :
    (flatOn V c).support = (V.1 : Set (Euclidean n)) := by
  rw [flatOn, measure_support_smul _ hc.ne']
  apply Set.Subset.antisymm
  · intro x hx
    have h := (Measure.support_restrict_subset hx).1
    rwa [V.1.closed_of_finiteDimensional.closure_eq] at h
  · intro x hx
    apply Metric.nhds_basis_ball.mem_measureSupport.mpr
    intro r hr
    simpa only [flatOn, one_smul] using
      (flatOn_ball_pos V (c := 1) zero_lt_one hx hr)

theorem regular_unitFlat (V : Plane m n) : (unitFlat V).Regular := by
  letI : (flatOn V 1).Regular := regular_flatOn V ENNReal.one_ne_top
  have hB : flatOn V 1 (closedBall 0 1) ≠ 0 :=
    ((flatOn_ball_pos V (c := 1) zero_lt_one V.1.zero_mem zero_lt_one).trans_le
      (measure_mono ball_subset_closedBall)).ne'
  exact Measure.Regular.smul (ENNReal.inv_ne_top.mpr hB)

theorem unitFlat_support (V : Plane m n) : (unitFlat V).support = (V.1 : Set (Euclidean n)) := by
  letI : (flatOn V 1).Regular := regular_flatOn V ENNReal.one_ne_top
  have hB : flatOn V 1 (closedBall 0 1) ≠ ∞ :=
    (isCompact_closedBall (0 : Euclidean n) 1).measure_lt_top.ne
  rw [unitFlat, measure_support_smul _ (ENNReal.inv_ne_zero.mpr hB), flatOn_support V zero_lt_one]

theorem isFlat_unitFlat (V : Plane m n) : IsFlat m (unitFlat V) := by
  letI : (flatOn V 1).Regular := regular_flatOn V ENNReal.one_ne_top
  have hBpos : 0 < flatOn V 1 (closedBall 0 1) :=
    (flatOn_ball_pos V (c := 1) zero_lt_one V.1.zero_mem zero_lt_one).trans_le
      (measure_mono ball_subset_closedBall)
  have hBfin : flatOn V 1 (closedBall 0 1) ≠ ∞ :=
    (isCompact_closedBall (0 : Euclidean n) 1).measure_lt_top.ne
  refine ⟨V, (flatOn V 1 (closedBall 0 1))⁻¹, ENNReal.inv_pos.mpr hBfin,
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hBpos.ne'), ?_⟩
  simp only [unitFlat, flatOn, one_smul]

theorem unitFlat_ne_zero (V : Plane m n) : unitFlat V ≠ 0 := by
  intro hz
  have hx : (0 : Euclidean n) ∈ (unitFlat V).support := by
    rw [unitFlat_support]
    exact V.1.zero_mem
  simpa [hz] using hx

end Preiss
