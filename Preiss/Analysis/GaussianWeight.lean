module
public import Preiss.Analysis.GaussianGrowth
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-! # Finite Gaussian weighting of measures with polynomial growth -/

open MeasureTheory Filter Set
open scoped ENNReal BigOperators
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

theorem integrable_exp_inner_mul_gaussian_parameter {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (w : Euclidean n) (t s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) * Real.exp (t * inner ℝ z w)) μ := by
  have hint : Integrable (fun z : Euclidean n => Real.exp (-(s / 2) * ‖z‖ ^ 2)) μ := by
    simpa only [pow_zero, one_mul] using
      integrable_norm_pow_mul_gaussian_of_ball_bound μ C p hgrowth.1 hgrowth.2.2
        0 (s / 2) (half_pos hs)
  apply (hint.const_mul (Real.exp ((|t| * ‖w‖) ^ 2 / (2*s)))).mono'
  · exact (show Continuous (fun z : Euclidean n =>
        Real.exp (-s * ‖z‖ ^ 2) * Real.exp (t * inner ℝ z w)) by fun_prop).aestronglyMeasurable
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
    have hden : (|t| * ‖w‖)^2 / (2*s) * (2*s) = (|t| * ‖w‖)^2 :=
      div_mul_cancel₀ _ (ne_of_gt (mul_pos two_pos hs))
    have hmul := mul_le_mul_of_nonneg_left hinner (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs.le)
    nlinarith [sq_nonneg (|t| * ‖w‖ - s*‖z‖)]

theorem integrable_exp_abs_inner_mul_gaussian_parameter {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (w : Euclidean n) (t s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) * Real.exp |t * inner ℝ z w|) μ := by
  have hp := integrable_exp_inner_mul_gaussian_parameter μ C p hgrowth w t s hs
  have hn := integrable_exp_inner_mul_gaussian_parameter μ C p hgrowth w (-t) s hs
  apply (hp.fun_add hn).mono'
  · exact (show Continuous (fun z : Euclidean n =>
      Real.exp (-s * ‖z‖ ^ 2) * Real.exp |t * inner ℝ z w|) by fun_prop).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases h : 0 ≤ t * inner ℝ z w
    · rw [abs_of_nonneg h]
      exact le_add_of_nonneg_right (by positivity)
    · rw [abs_of_neg (lt_of_not_ge h), ← neg_mul]
      exact le_add_of_nonneg_left (by positivity)

theorem hasSum_integral_gaussian_exp_inner {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hgrowth : HasPolynomialGrowthBound μ C p)
    (w : Euclidean n) (t s : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℕ => t ^ k / (k.factorial : ℝ) *
      ∫ z, (inner ℝ z w)^k * Real.exp (-s*‖z‖^2) ∂μ)
      (∫ z, Real.exp (-s*‖z‖^2) * Real.exp (t * inner ℝ z w) ∂μ) ∧
    Summable (fun k : ℕ => |t ^ k / (k.factorial : ℝ) *
      ∫ z, (inner ℝ z w)^k * Real.exp (-s*‖z‖^2) ∂μ|) := by
  let F (k : ℕ) (z : Euclidean n) :=
    (t*inner ℝ z w)^k / (k.factorial : ℝ) * Real.exp (-s*‖z‖^2)
  let B (k : ℕ) (z : Euclidean n) :=
    |t*inner ℝ z w|^k / (k.factorial : ℝ) * Real.exp (-s*‖z‖^2)
  have hseries (u : ℝ) : HasSum (fun k : ℕ => u^k/(k.factorial : ℝ)) (Real.exp u) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp u
  have hF (k : ℕ) : Continuous (F k) := by dsimp [F]; fun_prop
  have hB (k : ℕ) : Continuous (B k) := by dsimp [B]; fun_prop
  have hBn (k : ℕ) (z : Euclidean n) : 0 ≤ B k z := by dsimp [B]; positivity
  have hnorm (k : ℕ) (z : Euclidean n) : ‖F k z‖ = B k z := by
    simp only [F,B,Real.norm_eq_abs,abs_mul,abs_div,abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ (k.factorial : ℝ) from Nat.cast_nonneg _),abs_of_pos (Real.exp_pos _)]
  have hBs (z : Euclidean n) : HasSum (fun k => B k z)
      (Real.exp |t*inner ℝ z w| * Real.exp (-s*‖z‖^2)) :=
    (hseries |t*inner ℝ z w|).mul_right _
  have hBi : Integrable (fun z => ∑' k, B k z) μ := by
    simp_rw [(hBs _).tsum_eq]
    simpa only [mul_comm] using
      integrable_exp_abs_inner_mul_gaussian_parameter μ C p hgrowth w t s hs
  have hFs (z : Euclidean n) : HasSum (fun k => F k z)
      (Real.exp (-s*‖z‖^2) * Real.exp (t*inner ℝ z w)) := by
    simpa only [mul_comm] using (hseries (t*inner ℝ z w)).mul_right (Real.exp (-s*‖z‖^2))
  have hFI := hasSum_integral_of_dominated_convergence B
    (fun k => (hF k).aestronglyMeasurable)
    (fun k => ae_of_all μ (fun z => (hnorm k z).le))
    (ae_of_all μ (fun z => (hBs z).summable)) hBi (ae_of_all μ hFs)
  have hBI := hasSum_integral_of_dominated_convergence B
    (fun k => (hB k).aestronglyMeasurable)
    (fun k => ae_of_all μ (fun z => (Real.norm_of_nonneg (hBn k z)).le))
    (ae_of_all μ (fun z => (hBs z).summable)) hBi (ae_of_all μ hBs)
  have habs : Summable (fun k => |∫ z, F k z ∂μ|) :=
    hBI.summable.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_abs]
      calc
        |∫ z, F k z ∂μ| = ‖∫ z, F k z ∂μ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z, ‖F k z‖ ∂μ := norm_integral_le_integral_norm _
        _ = _ := integral_congr_ae (ae_of_all μ (hnorm k)))
  have heq (k : ℕ) : (∫ z, F k z ∂μ) = t^k/(k.factorial : ℝ) *
      ∫ z, (inner ℝ z w)^k * Real.exp (-s*‖z‖^2) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [F]
    rw [mul_pow]
    ring
  simp_rw [heq] at hFI habs
  exact ⟨hFI,habs⟩


end Preiss
