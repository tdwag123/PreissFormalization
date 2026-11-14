import Preiss.Density.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Converting diameter-normalized densities to radius-power limits -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss

theorem tendsto_radiusPowerRatio_of_densityRatio
    {X : Type*} [PseudoMetricSpace X] (m : ℕ) (μ : OuterMeasure X) (x : X)
    {θ : ℝ≥0∞}
    (h : Tendsto (dimensional_density_ratio μ (m : ℝ) x) (𝓝[>] 0) (𝓝 θ)) :
    Tendsto (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((2 : ℝ) ^ m) * θ)) := by
  let A : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ m)
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) m)).ne'
  have hAinf : A ≠ ∞ := ENNReal.ofReal_ne_top
  have ht := ENNReal.Tendsto.const_mul h (Or.inr hAinf)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [dimensional_density_ratio_closedBall μ (m : ℝ) x hr.le]
  have hden : ENNReal.ofReal ((2 * r) ^ (m : ℝ)) = A * ENNReal.ofReal (r ^ m) := by
    rw [Real.rpow_natCast, mul_pow, ENNReal.ofReal_mul (by positivity)]
  rw [hden, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hA0 hAinf]

theorem HasPositiveFiniteDensityAt.exists_radiusPowerDensity
    {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : ℕ}
    {μ : Measure X} {x : X} (h : HasPositiveFiniteDensityAt m μ x) :
    ∃ q : ℝ, 0 < q ∧ Tendsto
      (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal q)) := by
  obtain ⟨θ, hθ⟩ := h.hasDensity.exists_tendsto
  have hθpos : 0 < θ := by
    rw [← hθ.liminf_eq]
    exact h.1
  have hθfin : θ ≠ ∞ := by
    rw [← hθ.limsup_eq]
    exact h.2.2.ne
  refine ⟨(2 : ℝ) ^ m * θ.toReal, mul_pos (by positivity)
    (ENNReal.toReal_pos hθpos.ne' hθfin), ?_⟩
  have ht := tendsto_radiusPowerRatio_of_densityRatio m μ.toOuterMeasure x hθ
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hθfin]
  exact ht

end Preiss
