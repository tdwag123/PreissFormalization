import FormalizingGMT.Densities.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Zero-dimensional densities detect atoms -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem tendsto_densityRatio_zero (μ : Measure X) [IsLocallyFiniteMeasure μ] (x : X) :
    Tendsto (dimensional_density_ratio μ.toOuterMeasure 0 x) (𝓝[>] 0) (𝓝 (μ {x})) := by
  have ht : Tendsto (fun r : ℝ => μ (closedBall x r)) (𝓝[>] 0) (𝓝 (μ {x})) := by
    simpa only [Function.comp_def, biInter_gt_closedBall, closedBall_zero] using
      (tendsto_measure_biInter_gt
        (fun r (_ : 0 < r) => measurableSet_closedBall.nullMeasurableSet)
        (fun i j (_ : 0 < i) hij => closedBall_subset_closedBall hij)
        ⟨1, zero_lt_one, measure_closedBall_lt_top.ne⟩ :
        Tendsto (μ ∘ fun r : ℝ => closedBall x r) (𝓝[>] 0)
          (𝓝 (μ (⋂ r > (0 : ℝ), closedBall x r))))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp [dimensional_density_ratio, closedEBall_ofReal (le_of_lt hr)]

theorem lowerDensity_zero_eq_singleton (μ : Measure X) [IsLocallyFiniteMeasure μ] (x : X) :
    dimensional_lower_density μ.toOuterMeasure 0 x = μ {x} :=
  (tendsto_densityRatio_zero μ x).liminf_eq

end Preiss
