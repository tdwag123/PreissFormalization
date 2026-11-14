module
public import Preiss.Analysis.GaussianGrowth
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-! # Finite Gaussian weighting of measures with polynomial growth -/

open MeasureTheory Filter Set
open scoped ENNReal
namespace Preiss

theorem isFiniteMeasure_withDensity_gaussian {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p) :
    IsFiniteMeasure (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)))) := by
  have hint : Integrable (fun z : Euclidean n => Real.exp (-‖z‖ ^ 2)) μ := by
    simpa only [pow_zero, one_mul, neg_one_mul] using
      integrable_norm_pow_mul_gaussian_of_ball_bound μ C p hgrowth.1 hgrowth.2.2 0 1 zero_lt_one
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => (Real.exp_pos (-‖z‖ ^ 2)).le)]
  exact ENNReal.ofReal_ne_top

theorem integrable_exp_inner_mul_gaussian {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (w : Euclidean n) (t : ℝ) :
    Integrable (fun z => Real.exp (-‖z‖ ^ 2) * Real.exp (t * inner ℝ z w)) μ := by
  have hint : Integrable (fun z : Euclidean n => Real.exp (-(1 / 2 : ℝ) * ‖z‖ ^ 2)) μ := by
    simpa only [pow_zero, one_mul] using
      integrable_norm_pow_mul_gaussian_of_ball_bound μ C p hgrowth.1 hgrowth.2.2
        0 (1 / 2) (by norm_num)
  apply (hint.const_mul (Real.exp ((|t| * ‖w‖) ^ 2 / 2))).mono'
  · exact (show Continuous (fun z : Euclidean n =>
        Real.exp (-‖z‖ ^ 2) * Real.exp (t * inner ℝ z w)) by fun_prop).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (by positivity), ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hinner : t * inner ℝ z w ≤ |t| * ‖z‖ * ‖w‖ := by
      calc
        _ ≤ |t * inner ℝ z w| := le_abs_self _
        _ = |t| * |inner ℝ z w| := abs_mul _ _
        _ ≤ |t| * (‖z‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z w) (abs_nonneg t)
        _ = _ := by ring
    nlinarith [sq_nonneg (|t| * ‖w‖ - ‖z‖)]

theorem integrable_exp_inner_withDensity_gaussian {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (w : Euclidean n) (t : ℝ) :
    Integrable (fun z => Real.exp (t * inner ℝ z w))
      (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)))) := by
  rw [integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun z : Euclidean n => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2))) by fun_prop)
    (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using
    integrable_exp_inner_mul_gaussian μ C p hgrowth w t

end Preiss
