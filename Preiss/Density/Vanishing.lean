import FormalizingGMT.Densities.Basic

/-! # Vanishing dimensional upper density at any fixed positive ball scale -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

noncomputable section
namespace Preiss

theorem tendsto_scaled_ball_mass_div_pow_zero_of_upperDensity_eq_zero
    {X : Type*} [PseudoMetricSpace X] (m : ℕ) (ν : OuterMeasure X) (x : X)
    {c : ℝ} (hc : 0 < c)
    (hzero : dimensional_upper_density ν (m : ℝ) x = 0) :
    Tendsto (fun r : ℝ ↦ ν (ball x (c * r)) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 0) := by
  have hlo : dimensional_lower_density ν (m : ℝ) x = 0 :=
    le_antisymm ((lower_le_upper_density (μ := ν) (m : ℝ) x).trans_eq hzero) bot_le
  have ht : Tendsto (dimensional_density_ratio ν (m : ℝ) x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_liminf_eq_limsup hlo hzero
  have hscale : Tendsto (fun r : ℝ ↦ c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [mul_zero] using (tendsto_const_nhds.mul hid)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hc hr
  let A : ℝ≥0∞ := ENNReal.ofReal ((2 * c) ^ m)
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) m)).ne'
  have hAinf : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hmajor : Tendsto (fun r : ℝ ↦ A * dimensional_density_ratio ν (m : ℝ) x (c * r))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using ENNReal.Tendsto.const_mul (ht.comp hscale) (Or.inr hAinf)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [self_mem_nhdsWithin] with r hr
    rw [dimensional_density_ratio_closedBall ν (m : ℝ) x (mul_pos hc hr).le]
    have hden : ENNReal.ofReal ((2 * (c * r)) ^ (m : ℝ)) = A * ENNReal.ofReal (r ^ m) := by
      rw [Real.rpow_natCast, ← mul_assoc, mul_pow, ENNReal.ofReal_mul (by positivity)]
    rw [hden, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hA0 hAinf]
    exact ENNReal.div_le_div_right (ν.mono ball_subset_closedBall) _

end Preiss
