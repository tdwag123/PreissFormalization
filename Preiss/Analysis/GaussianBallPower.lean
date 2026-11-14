module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Gaussian integration from a power law for centered balls

This argument needs a centered ball law, not translation invariance or uniformity.
The exponential-tail identity and nonnegative Fubini avoid constructing a radial density.
-/

@[expose] public section
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_exp_neg_Ici (a : ℝ) :
    (∫⁻ t in Ici a, ENNReal.ofReal (Real.exp (-t))) = ENNReal.ofReal (Real.exp (-a)) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi a) := by
    simpa only [neg_one_mul] using exp_neg_integrableOn_Ioi a (b := 1) zero_lt_one
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-t)) t := by
    convert! (hasDerivAt_id t).neg.exp.neg using 1 <;> simp
  have ht : Tendsto (fun t : ℝ => -Real.exp (-t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Pi.neg_apply, neg_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg
  have hval : (∫ t in Ioi a, Real.exp (-t)) = Real.exp (-a) := by
    simpa only [zero_sub, neg_neg] using
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hint ht
  rw [← restrict_Ioi_eq_restrict_Ici,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun t => (Real.exp_pos _).le)), hval]

theorem lintegral_gaussian_of_closedBall_power
    (ρ : Measure (E)) [SFinite ρ] (C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d)
    (hball : ∀ r : ℝ, 0 < r → ρ (closedBall 0 r) = ENNReal.ofReal (C * r ^ d)) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) ∂ρ) =
      ENNReal.ofReal (Real.Gamma (d / 2 + 1) * C) := by
  classical
  let H (z : E) (t : ℝ) : ℝ≥0∞ :=
    if ‖z‖ ^ 2 ≤ t then ENNReal.ofReal (Real.exp (-t)) else 0
  have hH : Measurable (Function.uncurry H) := by
    apply Measurable.ite
    · exact measurableSet_le (measurable_fst.norm.pow_const 2) measurable_snd
    · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_snd.neg)
    · exact measurable_const
  have htail (z : E) :
      (∫⁻ t in Ici (0 : ℝ), H z t) = ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) := by
    change (∫⁻ t in Ici (0 : ℝ),
      (Ici (‖z‖ ^ 2)).indicator (fun t => ENNReal.ofReal (Real.exp (-t))) t) = _
    rw [lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (Ici_subset_Ici.mpr (sq_nonneg ‖z‖)), lintegral_exp_neg_Ici]
  have hsection (t : ℝ) :
      (∫⁻ z, H z t ∂ρ) = ENNReal.ofReal (Real.exp (-t)) * ρ {z | ‖z‖ ^ 2 ≤ t} := by
    change (∫⁻ z, ({z : E | ‖z‖ ^ 2 ≤ t}).indicator
      (fun _ => ENNReal.ofReal (Real.exp (-t))) z ∂ρ) = _
    exact lintegral_indicator_const (measurableSet_le (measurable_norm.pow_const 2) measurable_const) _
  have hsection_pos (t : ℝ) (ht : 0 < t) :
      (∫⁻ z, H z t ∂ρ) = ENNReal.ofReal (C * (Real.exp (-t) * t ^ (d / 2))) := by
    have hset : {z : E | ‖z‖ ^ 2 ≤ t} = closedBall 0 (Real.sqrt t) := by
      ext z
      simp only [mem_setOf_eq, mem_closedBall, dist_zero_right]
      exact (Real.le_sqrt (norm_nonneg z) ht.le).symm
    rw [hsection, hset, hball (Real.sqrt t) (Real.sqrt_pos.mpr ht),
      ← Real.rpow_div_two_eq_sqrt d ht.le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [← mul_assoc, mul_comm (Real.exp (-t)) C, mul_assoc]
  have hexponent : 0 < d / 2 + 1 :=
    add_pos (div_pos hd zero_lt_two) zero_lt_one
  have hGamma : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (d / 2)) (Ioi 0) := by
    simpa only [add_sub_cancel_right] using Real.GammaIntegral_convergent hexponent
  have hGammaVal : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (d / 2)) =
      Real.Gamma (d / 2 + 1) := by
    simpa only [add_sub_cancel_right] using (Real.Gamma_eq_integral hexponent).symm
  calc
    _ = ∫⁻ z, (∫⁻ t in Ici (0 : ℝ), H z t) ∂ρ := lintegral_congr (fun z => (htail z).symm)
    _ = ∫⁻ t in Ici (0 : ℝ), ∫⁻ z, H z t ∂ρ := lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ z, H z t ∂ρ := by rw [restrict_Ioi_eq_restrict_Ici]
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * (Real.exp (-t) * t ^ (d / 2))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hsection_pos t ht
    _ = ENNReal.ofReal (C * ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (d / 2)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hGamma.const_mul C), integral_const_mul]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hC (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _))
    _ = _ := by rw [hGammaVal, mul_comm C]

theorem integral_gaussian_of_closedBall_power
    (ρ : Measure (E)) [SFinite ρ] (C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d)
    (hball : ∀ r : ℝ, 0 < r → ρ (closedBall 0 r) = ENNReal.ofReal (C * r ^ d)) :
    Integrable (fun z => Real.exp (-‖z‖ ^ 2)) ρ ∧
      (∫ z, Real.exp (-‖z‖ ^ 2) ∂ρ) = Real.Gamma (d / 2 + 1) * C := by
  have hn : 0 ≤ᵐ[ρ] (fun z => Real.exp (-‖z‖ ^ 2)) :=
    ae_of_all _ (fun z => (Real.exp_pos _).le)
  have hval := lintegral_gaussian_of_closedBall_power ρ C d hC hd hball
  have hint : Integrable (fun z => Real.exp (-‖z‖ ^ 2)) ρ := by
    refine ⟨(Real.continuous_exp.comp (continuous_norm.pow 2).neg).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr ?_⟩
    rw [hval]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have hnonneg : 0 ≤ Real.Gamma (d / 2 + 1) * C :=
    mul_nonneg (Real.Gamma_pos_of_pos (add_pos (div_pos hd zero_lt_two) zero_lt_one)).le hC
  have heq := congrArg ENNReal.toReal
    ((ofReal_integral_eq_lintegral_ofReal hint hn).trans hval)
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun z => (Real.exp_pos _).le)),
    ENNReal.toReal_ofReal hnonneg] using heq

end Preiss
