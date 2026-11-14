import Preiss.Density.Defs
import Mathlib.Tactic

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Preiss

theorem HasPositiveFiniteDensityAt.smul
    {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : ℕ}
    {μ : Measure X} {x : X} (h : HasPositiveFiniteDensityAt m μ x)
    {c : ℝ≥0∞} (hc : 0 < c) (hctop : c < ∞) :
    HasPositiveFiniteDensityAt m (c • μ) x := by
  obtain ⟨θ, hθ⟩ := h.hasDensity.exists_tendsto
  have hθpos : 0 < θ := by
    rw [← hθ.liminf_eq]
    exact h.1
  have hθfin : θ < ∞ := by
    rw [← hθ.limsup_eq]
    exact h.2.2
  have hlim : Tendsto (dimensional_density_ratio (c • μ).toOuterMeasure (m : ℝ) x)
      (𝓝[>] 0) (𝓝 (c * θ)) := by
    have hh := ENNReal.Tendsto.const_mul hθ (Or.inr hctop.ne)
    apply hh.congr
    intro r
    change c * (μ (Metric.closedEBall x (ENNReal.ofReal r)) /
      ENNReal.ofReal ((2*r)^(m : ℝ))) =
      (c • μ) (Metric.closedEBall x (ENNReal.ofReal r)) /
        ENNReal.ofReal ((2*r)^(m : ℝ))
    rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  have hlo : dimensional_lower_density (c • μ).toOuterMeasure (m : ℝ) x = c * θ :=
    hlim.liminf_eq
  have hup : dimensional_upper_density (c • μ).toOuterMeasure (m : ℝ) x = c * θ :=
    hlim.limsup_eq
  refine ⟨?_, hlo.trans hup.symm, ?_⟩
  · rw [hlo]
    exact ENNReal.mul_pos_iff.mpr ⟨hc, hθpos⟩
  · rw [hup]
    exact ENNReal.mul_lt_top hctop hθfin

end Preiss

#print axioms Preiss.HasPositiveFiniteDensityAt.smul
