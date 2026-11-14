import Preiss.Tangent.Compactness
import Preiss.Geometry.FlatMeasure
import Preiss.Rectifiability.WeakApproximation.Defs
import Preiss.Geometry.PlaneMeasure
import Preiss.Geometry.PlaneRegularity
import Preiss.Analysis.Vague.CompactMass
import Preiss.Geometry.Cones

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem tendsto_mass_outside_tube_of_flat_limit
    (ν : ℕ → Measure (Euclidean n)) (hν : ∀ i, (ν i).Regular)
    (V : Plane m n) {c : ℝ≥0∞} (hc : 0 < c) (hcfin : c < ∞)
    (hlim : Measure.WeaklyConverges ν (flatOn V c)) {η R : ℝ}
    (hη : 0 < η) (hR : 0 < R) :
    Tendsto (fun i ↦ ν i (closedBall 0 R ∩
      {z | η ≤ infDist z (V.1 : Set (Euclidean n))})) atTop (𝓝 0) := by
  let K : Set (Euclidean n) := closedBall 0 R ∩
    {z | η ≤ infDist z (V.1 : Set (Euclidean n))}
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right
    (isClosed_le continuous_const (continuous_infDist_pt _))
  apply tendsto_mass_compact_null_of_vague ν (flatOn V c) hν
    (regular_flatOn V hcfin.ne) hlim hK
  have hempty : K ∩ (V.1 : Set (Euclidean n)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hd : infDist z (V.1 : Set (Euclidean n)) = 0 := infDist_zero_of_mem hz.2
    exact (not_le_of_gt hη) (hd ▸ hz.1.2)
  rw [flatOn, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hK.measurableSet,
    hempty, measure_empty, mul_zero]


theorem eventually_ball_mass_lower_bound_of_flat_limit
    (ν : ℕ → Measure (Euclidean n)) (hν : ∀ i, (ν i).Regular)
    (V : Plane m n) {c : ℝ≥0∞} (hc : 0 < c) (hcfin : c < ∞)
    (hlim : Measure.WeaklyConverges ν (flatOn V c)) {η R : ℝ}
    (hη : 0 < η) (hR : 0 < R) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ i in atTop, ∀ z : Euclidean n,
      z ∈ V.1 → z ∈ closedBall 0 R → ENNReal.ofReal a ≤ ν i (ball z η) := by
  have hK : IsCompact (closedBall (0 : Euclidean n) R ∩ (V.1 : Set (Euclidean n))) :=
    (isCompact_closedBall 0 R).inter_right V.1.closed_of_finiteDimensional
  obtain ⟨a, ha, he⟩ := eventually_uniform_ball_mass_lower_bound_of_vague ν (flatOn V c)
    hν (regular_flatOn V hcfin.ne) hlim hK hη
    (fun z hz => flatOn_ball_pos V hc hz.2 (by linarith))
  refine ⟨a, ha, ?_⟩
  filter_upwards [he] with i hi z hzV hzB
  exact hi z ⟨hzB, hzV⟩


theorem weaklyLinearlyApproximableAt_of_all_tangents_flat
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensitiesAt m μ x)
    (ht : ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) :
    MeasureWeaklyLinearlyApproximableAt m μ x := by sorry

end Preiss
