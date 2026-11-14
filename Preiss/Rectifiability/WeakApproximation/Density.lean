import Preiss.Density.Vanishing
import Preiss.Rectifiability.WeakApproximation.Restriction

/-! # A density criterion for negligible deletion -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem negligibleDeletionAt_of_upperDensity_restrict_compl_eq_zero
    (μ : Measure (Euclidean n)) (F : Set (Euclidean n)) (hF : MeasurableSet F)
    (x : Euclidean n)
    (hzero : dimensional_upper_density (μ.restrict Fᶜ).toOuterMeasure (m : ℝ) x = 0) :
    negligibleDeletionAt m μ F x := by
  have h := tendsto_scaled_ball_mass_div_pow_zero_of_upperDensity_eq_zero m
    (μ.restrict Fᶜ).toOuterMeasure x (show (0 : ℝ) < 2 by norm_num) hzero
  change Tendsto (fun r : ℝ ↦ (μ.restrict Fᶜ) (ball x (2 * r)) / ENNReal.ofReal (r ^ m))
    (𝓝[>] 0) (𝓝 0) at h
  simpa only [negligibleDeletionAt, Measure.restrict_apply isOpen_ball.measurableSet, sdiff_eq] using h

end Preiss
