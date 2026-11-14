import Preiss.Density.Defs
import Preiss.Density.PowerComparison
import Preiss.Density.UpperBounds

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem absolutelyContinuous_hausdorff_of_upper_density_finite
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, dimensional_upper_density μ.toOuterMeasure (m : ℝ) x < ∞) :
    μ ≪ (Measure.hausdorffMeasure (m : ℝ)) := by
  let S : ℕ × ℕ → Set (Euclidean n) := fun i => goodBallSet (m : ℝ) ((i.1 : ℝ) + 1) i.2 μ
  have hS (i : ℕ × ℕ) : MeasurableSet (S i) := (isClosed_goodBallSet _ _ _ μ).measurableSet
  have hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, S i := by
    filter_upwards [h] with x hx
    obtain ⟨j, k, hjk⟩ := exists_goodBallSet_mem_of_upperDensity_lt_top μ x hx
    exact mem_iUnion.mpr ⟨(j, k), hjk⟩
  intro t ht
  have hnull (i : ℕ × ℕ) : μ (t ∩ S i) = 0 := by
    have hbound : μ.restrict (S i) ≤ ENNReal.ofReal ((i.1 : ℝ) + 1) •
        (Measure.hausdorffMeasure (m : ℝ)).restrict (S i) := by
      apply measure_restrict_le_hausdorff_of_uniform_ball_upper_bound m μ (S i) (hS i)
        ((i.1 : ℝ) + 1) (1 / ((i.2 : ℝ) + 1)) (by positivity) (by positivity)
      intro x hx r hr hrR
      exact (measure_mono ball_subset_closedBall).trans
        (by simpa only [Real.rpow_natCast] using hx x r hr hrR (mem_closedBall_self hr.le))
    have hle := Measure.le_iff'.mp hbound t
    have htS : (Measure.hausdorffMeasure (m : ℝ)) (t ∩ S i) = 0 :=
      measure_mono_null inter_subset_left ht
    simpa only [Measure.restrict_apply' (hS i), Measure.smul_apply, smul_eq_mul,
      htS, mul_zero, nonpos_iff_eq_zero] using hle
  have hnullUnion : μ (⋃ i, t ∩ S i) = 0 := measure_iUnion_null hnull
  have hnullOutside : μ (⋃ i, S i)ᶜ = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcover] with x hx
    exact fun hxnot => hxnot hx
  apply measure_mono_null (t := (⋃ i, t ∩ S i) ∪ (⋃ i, S i)ᶜ) ?_
    (measure_union_null hnullUnion hnullOutside)
  intro x hx
  by_cases hxc : x ∈ ⋃ i, S i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hxc
    exact Or.inl (mem_iUnion.mpr ⟨i, hx, hi⟩)
  · exact Or.inr hxc

end Preiss
