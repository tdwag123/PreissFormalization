module
public import Preiss.Uniform.MomentForms
public import Preiss.Uniform.Defs
public import Preiss.Analysis.GaussianGrowth
public import Preiss.Analysis.GaussianWeight
public import Preiss.Analysis.GaussianBallPowerParameter
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
open MeasureTheory Metric
open scoped BigOperators
namespace Preiss
variable {n m : ℕ}

theorem IsUnitUniform.hasPolynomialGrowthBound (μ : Measure (Euclidean n))
    (hμ : IsUnitUniform m μ) : HasPolynomialGrowthBound μ 1 (m : ℝ) := by
  refine ⟨by positivity, by positivity, ?_⟩
  intro R hR
  rw [hμ.2.2 0 hμ.2.1 R hR]
  apply ENNReal.ofReal_le_ofReal
  rw [one_mul, Real.rpow_natCast]
  exact pow_le_pow_left₀ hR.le (by linarith) m

theorem integrable_gaussianMomentKernel_of_integrable_norm
    (μ : Measure (Euclidean n)) (k : ℕ) (s : ℝ)
    (hint : Integrable (fun z => ‖z‖ ^ k * Real.exp (-s * ‖z‖ ^ 2)) μ) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z) μ := by
  apply hint.mono'
  · have hweight : Continuous (fun z : Euclidean n => Real.exp (-s * ‖z‖ ^ 2)) := by
      fun_prop
    exact (hweight.smul (continuous_momentKernel k)).aestronglyMeasurable
  · filter_upwards [] with z
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left (norm_momentKernel_le k z)
      (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem integrable_gaussianMomentKernel (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z) μ := by
  exact integrable_gaussianMomentKernel_of_integrable_norm μ k s
    (integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ.1 1 (m : ℝ)
      (IsUnitUniform.hasPolynomialGrowthBound μ hμ) k s hs)

theorem gaussianMass_unitUniform (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (s : ℝ) (hs : 0 < s) :
    gaussianMass μ s = Real.Gamma ((m : ℝ) / 2 + 1) * s ^ (-((m : ℝ) / 2)) := by
  letI : μ.Regular := hμ.1
  have hball (r : ℝ) (hr : 0 < r) :
      μ (closedBall 0 r) = ENNReal.ofReal ((1 : ℝ) * r ^ (m : ℝ)) := by
    simpa only [one_mul, Real.rpow_natCast] using hμ.2.2 0 hμ.2.1 r hr
  simpa only [gaussianMass, mul_one] using
    (integral_gaussian_parameter_of_closedBall_power μ 1 (m : ℝ) zero_le_one
      (Nat.cast_pos.mpr hm) hball s hs).2

theorem norm_gaussianMomentForm_le (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (Euclidean n)), IsUnitUniform m μ →
      ∀ k : ℕ, 0 < k → ∀ s : ℝ, 0 < s →
      ‖gaussianMomentForm μ k s‖ ≤ C * 2 ^ k * (k : ℝ) ^ ((k : ℝ) / 2) *
        s ^ ((k : ℝ) / 2) / (k.factorial : ℝ) := by
  refine ⟨(2 : ℝ) ^ ((m : ℝ) / 2), by positivity, ?_⟩
  intro μ hμ k hk s hs
  have hs2 : 0 < s / 2 := half_pos hs
  have hgrowth := IsUnitUniform.hasPolynomialGrowthBound μ hμ
  have hint (a : ℝ) (ha : 0 < a) (l : ℕ) :
      Integrable (fun z : Euclidean n => ‖z‖ ^ l * Real.exp (-a * ‖z‖ ^ 2)) μ :=
    integrable_norm_pow_mul_gaussian_of_ball_bound μ 1 (m : ℝ) hgrowth.1 hgrowth.2.2 l a ha
  have hmass : 0 < gaussianMass μ s := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)
  have hhalf : gaussianMass μ (s/2) = (2 : ℝ)^((m : ℝ)/2) * gaussianMass μ s := by
    rw [gaussianMass_unitUniform μ hm hμ (s/2) hs2,
      gaussianMass_unitUniform μ hm hμ s hs,
      Real.div_rpow hs.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  have hmoment : (∫ z, ‖z‖ ^ k * Real.exp (-s * ‖z‖ ^ 2) ∂μ) ≤
      ((k : ℝ)/s)^((k : ℝ)/2) * gaussianMass μ (s/2) := by
    have hgauss : Integrable (fun z : Euclidean n => Real.exp (-(s/2)*‖z‖^2)) μ := by
      simpa only [pow_zero, one_mul] using hint (s/2) hs2 0
    rw [gaussianMass, ← integral_const_mul]
    apply integral_mono (hint s hs k) (hgauss.const_mul _)
    intro z
    have he : Real.exp (-s * ‖z‖^2) =
        Real.exp (-(s/2)*‖z‖^2) * Real.exp (-(s/2)*‖z‖^2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (pow_mul_gaussian_half_le (norm_nonneg z) hs k hk)
      (Real.exp_pos _).le
  have hfac : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hcoef : 0 ≤ (2*s)^k / (k.factorial : ℝ) * (gaussianMass μ s)⁻¹ := by positivity
  have hn : ‖gaussianMomentForm μ k s‖ ≤
      ((2*s)^k / (k.factorial : ℝ) * (gaussianMass μ s)⁻¹) *
        (∫ z, ‖z‖^k * Real.exp (-s*‖z‖^2) ∂μ) := by
    rw [gaussianMomentForm, norm_smul, Real.norm_of_nonneg hcoef]
    apply mul_le_mul_of_nonneg_left _ hcoef
    calc
      _ ≤ ∫ z, ‖Real.exp (-s*‖z‖^2) • momentKernel k z‖ ∂μ := norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_momentKernel, mul_comm]
  apply hn.trans
  apply (mul_le_mul_of_nonneg_left hmoment hcoef).trans_eq
  rw [hhalf, Real.div_rpow (Nat.cast_nonneg k) hs.le, mul_pow]
  have hsval : s ^ k = s ^ ((k : ℝ)/2) * s ^ ((k : ℝ)/2) := by
    rw [← Real.rpow_add hs]
    have h : (k : ℝ)/2 + (k : ℝ)/2 = k := by ring
    rw [h, Real.rpow_natCast]
  rw [hsval]
  have hsp : s ^ ((k : ℝ)/2) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  field_simp [hsp, hmass.ne', hfac.ne']
  <;> ring

theorem integral_gaussian_center_unitUniform (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (x : Euclidean n) (hx : x ∈ μ.support)
    (s : ℝ) (hs : 0 < s) :
    (∫ z, Real.exp (-s*‖z-x‖^2) ∂μ) = gaussianMass μ s := by
  letI : μ.Regular := hμ.1
  have hball (r : ℝ) (hr : 0 < r) :
      μ (closedBall x r) = ENNReal.ofReal ((1 : ℝ)*r^(m : ℝ)) := by
    simpa only [one_mul, Real.rpow_natCast] using hμ.2.2 x hx r hr
  have H := (integral_gaussian_center_parameter_of_closedBall_power μ x 1 (m : ℝ)
    zero_le_one (Nat.cast_pos.mpr hm) hball s hs).2
  rw [gaussianMass_unitUniform μ hm hμ s hs]
  simpa only [mul_one] using H

theorem integral_gaussian_exp_inner_unitUniform (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (x : Euclidean n) (hx : x ∈ μ.support)
    (s : ℝ) (hs : 0 < s) :
    (∫ z, Real.exp (-s*‖z‖^2) * Real.exp ((2*s)*inner ℝ z x) ∂μ) =
      Real.exp (s*‖x‖^2) * gaussianMass μ s := by
  rw [← integral_gaussian_center_unitUniform μ hm hμ x hx s hs, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← Real.exp_add, ← Real.exp_add, norm_sub_sq_real]
  congr 1
  ring

theorem hasSum_gaussianMoment_diagonal (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (x : Euclidean n) (hx : x ∈ μ.support)
    (s : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℕ => gaussianMomentForm μ k s (fun _ => x))
      (Real.exp (s * ‖x‖ ^ 2)) ∧
    Summable (fun k : ℕ => |gaussianMomentForm μ k s (fun _ => x)|) := by
  obtain ⟨hser,habs⟩ := hasSum_integral_gaussian_exp_inner μ 1 (m : ℝ)
    (IsUnitUniform.hasPolynomialGrowthBound μ hμ) x (2*s) s hs
  have hmass : 0 < gaussianMass μ s := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)
  have hident (k : ℕ) : gaussianMomentForm μ k s (fun _ => x) =
      (gaussianMass μ s)⁻¹ * ((2*s)^k/(k.factorial : ℝ) *
        ∫ z, (inner ℝ z x)^k * Real.exp (-s*‖z‖^2) ∂μ) := by
    rw [gaussianMomentForm_apply μ k s (integrable_gaussianMomentKernel μ hm hμ k s hs)]
    simp only [gaussianMoment, gaussianMass, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  simp_rw [hident]
  constructor
  · convert hser.mul_left (gaussianMass μ s)⁻¹ using 1
    rw [integral_gaussian_exp_inner_unitUniform μ hm hμ x hx s hs]
    field_simp [hmass.ne']
  · simpa only [abs_mul] using habs.mul_left |(gaussianMass μ s)⁻¹|

theorem gaussianMoment_taylor_remainder (hm : 0 < m) (q : ℕ) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (Euclidean n)), IsUnitUniform m μ →
      ∀ x ∈ μ.support, ∀ s : ℝ, 0 < s →
      |(∑ k ∈ Finset.range (2 * q), gaussianMomentForm μ (k + 1) s (fun _ => x)) -
        ∑ j ∈ Finset.range q, s ^ (j + 1) * ‖x‖ ^ (2 * (j + 1)) /
          ((j + 1).factorial : ℝ)| ≤ C * (s * ‖x‖ ^ 2) ^ ((q : ℝ) + 1 / 2) := by
  sorry

end Preiss
