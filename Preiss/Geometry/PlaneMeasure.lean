module

public import Preiss.Geometry.Planes
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def flatOn (V : Plane m n) (c : ℝ≥0∞) : Measure (Euclidean n) :=
  c • ((Measure.hausdorffMeasure (m : ℝ))).restrict (V.1 : Set (Euclidean n))

def unitFlat (V : Plane m n) : Measure (Euclidean n) :=
  (flatOn V 1 (closedBall 0 1))⁻¹ • flatOn V 1

theorem map_hausdorffMeasure_subtype_eq_restrict (V : Plane m n) :
    (Measure.hausdorffMeasure (m : ℝ) : Measure V.1).map
      (fun v : V.1 ↦ (v : Euclidean n)) =
      (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n)) := by
  have hi : Isometry (fun v : V.1 ↦ (v : Euclidean n)) := isometry_subtype_coe
  have hr : Set.range (fun v : V.1 ↦ (v : Euclidean n)) = (V.1 : Set (Euclidean n)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  simpa only [hr] using hi.map_hausdorffMeasure (Or.inl (Nat.cast_nonneg m))

theorem unitFlat_closedBall (V : Plane m n) (x : Euclidean n) (hx : x ∈ V.1)
    {r : ℝ} (hr : 0 < r) : unitFlat V (closedBall x r) = ENNReal.ofReal (r ^ m) := by
  let μV : Measure V.1 := Measure.hausdorffMeasure (m : ℝ)
  haveI : Measure.IsAddHaarMeasure μV := by
    dsimp [μV]
    simpa only [V.property] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ V.1 : ℝ) : Measure V.1))
  have hval : Measurable (fun v : V.1 ↦ (v : Euclidean n)) := continuous_subtype_val.measurable
  have hCB (v : V.1) (s : ℝ) :
      flatOn V 1 (closedBall (v : Euclidean n) s) = μV (closedBall v s) := by
    simp only [flatOn, one_smul]
    rw [← map_hausdorffMeasure_subtype_eq_restrict V,
      Measure.map_apply hval measurableSet_closedBall]
    rfl
  have hzero := hCB (0 : V.1) 1
  change flatOn V 1 (closedBall (0 : Euclidean n) 1) = μV (closedBall 0 1) at hzero
  have hn : flatOn V 1 (closedBall (0 : Euclidean n) 1) ≠ 0 := by
    rw [hzero]
    exact (measure_closedBall_pos μV (0 : V.1) zero_lt_one).ne'
  have hfin : flatOn V 1 (closedBall (0 : Euclidean n) 1) ≠ ∞ := by
    rw [hzero]
    exact (isCompact_closedBall (0 : V.1) 1).measure_lt_top.ne
  have hb : flatOn V 1 (closedBall x r) =
      ENNReal.ofReal (r ^ m) * flatOn V 1 (closedBall (0 : Euclidean n) 1) := by
    calc
      flatOn V 1 (closedBall x r) = μV (closedBall (⟨x, hx⟩ : V.1) r) := hCB ⟨x, hx⟩ r
      _ = ENNReal.ofReal (r ^ m) * μV (closedBall 0 1) := by
        simpa only [V.property] using Measure.addHaar_closedBall' μV (⟨x, hx⟩ : V.1) hr.le
      _ = _ := by rw [← hzero]
  rw [unitFlat, Measure.smul_apply, smul_eq_mul, hb, mul_left_comm,
    ENNReal.inv_mul_cancel hn hfin, mul_one]

theorem planeMeasure_ball_and_sphere (V : Plane m n) (hm : 0 < m) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : Euclidean n, x ∈ V.1 → ∀ r : ℝ, 0 < r →
      (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n)) (ball x r) =
        ENNReal.ofReal (b * r ^ m) ∧
      (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n)) (sphere x r) = 0 := by
  let μV : Measure V.1 := Measure.hausdorffMeasure (m : ℝ)
  haveI : Measure.IsAddHaarMeasure μV := by
    dsimp [μV]
    simpa only [V.property] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ V.1 : ℝ) : Measure V.1))
  have hval : Measurable (fun v : V.1 ↦ (v : Euclidean n)) := continuous_subtype_val.measurable
  have hpos : 0 < μV (ball 0 1) := measure_ball_pos μV (0 : V.1) zero_lt_one
  have hfin : μV (ball 0 1) < ∞ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (isCompact_closedBall (0 : V.1) 1).measure_lt_top
  refine ⟨(μV (ball 0 1)).toReal, ENNReal.toReal_pos hpos.ne' hfin.ne, ?_⟩
  intro x hx r hr
  have hball : (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n))
      (ball x r) = μV (ball (⟨x, hx⟩ : V.1) r) := by
    rw [← map_hausdorffMeasure_subtype_eq_restrict V,
      Measure.map_apply hval measurableSet_ball]
    rfl
  have hsphere : (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n))
      (sphere x r) = μV (sphere (⟨x, hx⟩ : V.1) r) := by
    rw [← map_hausdorffMeasure_subtype_eq_restrict V,
      Measure.map_apply hval isClosed_sphere.measurableSet]
    rfl
  constructor
  · rw [hball, Measure.addHaar_ball_of_pos μV (⟨x, hx⟩ : V.1) hr, V.property,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne, mul_comm]
  · rw [hsphere]
    exact Measure.addHaar_sphere_of_ne_zero μV (⟨x, hx⟩ : V.1) hr.ne'

end Preiss
