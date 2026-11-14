import FormalizingGMT.Densities.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # Lower density from a uniform lower power bound

The estimate works for arbitrary outer measures on pseudometric spaces.
The factor `2 ^ m` records the diameter normalization of GMT densities.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss

theorem lower_density_ge_of_ball_power_lower_bound
    {X : Type*} [PseudoMetricSpace X] (m : ℕ) (μ : OuterMeasure X) (x : X)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R)
    (hball : ∀ r : ℝ, 0 < r → r < R →
      ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r)) :
    ENNReal.ofReal (a / 2 ^ m) ≤ dimensional_lower_density μ (m : ℝ) x := by
  refine le_liminf_of_le (h := ?_)
  filter_upwards [Ioo_mem_nhdsGT hR] with r hrange
  have hr : 0 < r := hrange.1
  rw [dimensional_density_ratio_closedBall μ (m : ℝ) x hr.le]
  have hden : ENNReal.ofReal ((2 * r) ^ (m : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)).ne'
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden) (Or.inl ENNReal.ofReal_ne_top)).mpr
  have heq : ENNReal.ofReal (a / 2 ^ m) * ENNReal.ofReal ((2 * r) ^ (m : ℝ)) =
      ENNReal.ofReal (a * r ^ m) := by
    rw [← ENNReal.ofReal_mul (div_nonneg ha (by positivity)), Real.rpow_natCast, mul_pow]
    congr 1
    field_simp
  rw [heq]
  exact (hball r hr hrange.2).trans (measure_mono ball_subset_closedBall)

end Preiss
