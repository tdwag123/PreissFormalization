module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Hausdorff comparison from uniform upper bounds on balls

The target is an arbitrary metric space. Neither properness nor local finiteness
is needed: the assumed ball bounds provide the required control.
-/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace Preiss
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem measure_le_smul_hausdorff_of_diameter_bound (m : ℕ) (μ : Measure X)
    (c ε : ℝ≥0∞) (hc : c ≠ 0) (hctop : c ≠ ∞) (hε : 0 < ε)
    (h : ∀ t : Set X, ediam t ≤ ε → μ t ≤ c * ediam t ^ (m : ℝ)) :
    μ ≤ c • Measure.hausdorffMeasure (m : ℝ) := by
  have hn : c⁻¹ • μ ≤ Measure.hausdorffMeasure (m : ℝ) := by
    apply Measure.le_hausdorffMeasure (m : ℝ) (c⁻¹ • μ) ε hε
    intro t ht
    simp only [Measure.smul_apply, smul_eq_mul]
    calc
      c⁻¹ * μ t ≤ c⁻¹ * (c * ediam t ^ (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (h t ht) bot_le
      _ = ediam t ^ (m : ℝ) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc hctop, one_mul]
  apply Measure.le_iff'.mpr
  intro t
  have ht := mul_le_mul_of_nonneg_left (Measure.le_iff'.mp hn t) (show 0 ≤ c from bot_le)
  simpa only [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hc hctop, one_mul] using ht

theorem measure_restrict_le_hausdorff_of_uniform_ball_upper_bound
    (m : ℕ) (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (b R : ℝ) (hb : 0 < b) (hR : 0 < R)
    (hball : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r < R →
      μ (ball x r) ≤ ENNReal.ofReal (b * r ^ m)) :
    μ.restrict S ≤ ENNReal.ofReal b • (Measure.hausdorffMeasure (m : ℝ)).restrict S := by
  have hglobal : μ.restrict S ≤ ENNReal.ofReal b • Measure.hausdorffMeasure (m : ℝ) := by
    apply measure_le_smul_hausdorff_of_diameter_bound m (μ.restrict S)
      (ENNReal.ofReal b) (ENNReal.ofReal (R / 2))
      (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top (by positivity)
    intro t ht
    rw [Measure.restrict_apply' hS]
    rcases (t ∩ S).eq_empty_or_nonempty with hempty | ⟨x, hxt, hxS⟩
    · simp [hempty]
    have hfinite : ediam t ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ht
    have hdR : diam t < R := by
      have hd := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
      rw [ENNReal.toReal_ofReal (by positivity)] at hd
      change diam t ≤ R / 2 at hd
      linarith
    have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (b * r ^ m))
        (𝓝[>] (diam t)) (𝓝 (ENNReal.ofReal (b * diam t ^ m))) := by
      have hc : Continuous (fun r : ℝ => ENNReal.ofReal (b * r ^ m)) :=
        ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow m))
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hbound : μ (t ∩ S) ≤ ENNReal.ofReal (b * diam t ^ m) := by
      apply ge_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT hdR] with r hrange
      have hr : 0 < r := lt_of_le_of_lt diam_nonneg hrange.1
      exact (measure_mono (fun y hy =>
        (dist_le_diam_of_mem' hfinite hy.1 hxt).trans_lt hrange.1)).trans
        (hball x hxS r hr hrange.2)
    have heq : ENNReal.ofReal (b * diam t ^ m) =
        ENNReal.ofReal b * ediam t ^ (m : ℝ) := by
      rw [ENNReal.ofReal_mul hb.le, ENNReal.ofReal_pow diam_nonneg,
        diam, ENNReal.ofReal_toReal hfinite, ENNReal.rpow_natCast]
    exact hbound.trans_eq heq
  simpa only [Measure.restrict_restrict hS, inter_self, Measure.restrict_smul] using
    Measure.restrict_mono_measure hglobal S

end Preiss
