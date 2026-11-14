import Preiss.Uniform.GaussianNormBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

open MeasureTheory Filter Set
open scoped Topology
namespace Preiss

theorem gaussian_integral_bound_of_linear_growth
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (f : E → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ z ∂μ, |f z| ≤ C * (1 + ‖z‖))
    (s : ℝ)
    (h0 : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2)) μ)
    (h1 : Integrable (fun z => ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) μ) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) * f z) μ ∧
      |∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ| ≤
        C * ((∫ z, Real.exp (-s * ‖z‖ ^ 2) ∂μ) +
          ∫ z, ‖z‖ * Real.exp (-s * ‖z‖ ^ 2) ∂μ) := by
  have hdom := (h0.add h1).const_mul C
  have hnorm : ∀ᵐ z ∂μ, ‖Real.exp (-s * ‖z‖ ^ 2) * f z‖ ≤
      C * (Real.exp (-s * ‖z‖ ^ 2) + ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) := by
    filter_upwards [hbound] with z hz
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    calc
      Real.exp (-s * ‖z‖ ^ 2) * |f z| ≤
          Real.exp (-s * ‖z‖ ^ 2) * (C * (1 + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
      _ = _ := by ring
  have hmeas : Measurable (fun z : E => Real.exp (-s * ‖z‖ ^ 2) * f z) := by
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).measurable.mul hf
  have hint := hdom.mono' hmeas.aestronglyMeasurable hnorm
  refine ⟨hint, ?_⟩
  calc
    |∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ| =
        ‖∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ‖Real.exp (-s * ‖z‖ ^ 2) * f z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, C * (Real.exp (-s * ‖z‖ ^ 2) + ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) ∂μ :=
      integral_mono_ae hint.norm hdom hnorm
    _ = _ := by rw [integral_const_mul, integral_add h0 h1]

theorem normalized_gaussian_integral_tendsto_zero_of_linear_growth
    {m n : ℕ} (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (f : Euclidean n → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ z ∂μ, |f z| ≤ C * (1 + ‖z‖)) :
    Tendsto (fun s : ℝ => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ) (𝓝[>] 0) (𝓝 0) := by
  let K : ℝ := (2 : ℝ) ^ ((m : ℝ) / 2)
  have hestimate (s : ℝ) (hs : 0 < s) :
      ‖(s / gaussianMass μ s) * ∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ‖ ≤
        C * s + C * K * s ^ (1/2 : ℝ) := by
    have hint (j : ℕ) := integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ.1
      1 (m : ℝ) (IsUnitUniform.hasPolynomialGrowthBound μ hμ) j s hs
    have h0 : Integrable (fun z : Euclidean n => Real.exp (-s * ‖z‖ ^ 2)) μ := by
      simpa only [pow_zero, one_mul] using hint 0
    have h1 : Integrable (fun z : Euclidean n => ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) μ := by
      simpa only [pow_one] using hint 1
    have hmass : 0 < gaussianMass μ s := by
      rw [gaussianMass_unitUniform μ hm hμ s hs]
      exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)
    have hbound' := (gaussian_integral_bound_of_linear_growth μ f hf C hC hbound s h0 h1).2
    change |∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ| ≤
      C * (gaussianMass μ s + ∫ z, ‖z‖ * Real.exp (-s * ‖z‖ ^ 2) ∂μ) at hbound'
    have hmoment : (∫ z, ‖z‖ * Real.exp (-s * ‖z‖ ^ 2) ∂μ) ≤
        K * s ^ (-(1/2 : ℝ)) * gaussianMass μ s := by
      simpa only [K, Nat.cast_one, Real.one_rpow, pow_one, mul_one] using
        integral_norm_pow_mul_gaussian_le_unitUniform μ hm hμ 1 (by decide) s hs
    have hpow : s * s ^ (-(1/2 : ℝ)) = s ^ (1/2 : ℝ) := by
      calc
        s * s ^ (-(1/2 : ℝ)) = s ^ (1 : ℝ) * s ^ (-(1/2 : ℝ)) := by rw [Real.rpow_one]
        _ = s ^ (1/2 : ℝ) := by rw [← Real.rpow_add hs]; norm_num
    calc
      ‖(s / gaussianMass μ s) * ∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ‖ =
          (s / gaussianMass μ s) * |∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ| := by
        rw [norm_mul, Real.norm_of_nonneg (div_pos hs hmass).le, Real.norm_eq_abs]
      _ ≤ (s / gaussianMass μ s) *
          (C * (gaussianMass μ s + ∫ z, ‖z‖ * Real.exp (-s * ‖z‖ ^ 2) ∂μ)) :=
        mul_le_mul_of_nonneg_left hbound' (div_pos hs hmass).le
      _ ≤ (s / gaussianMass μ s) *
          (C * (gaussianMass μ s + K * s ^ (-(1/2 : ℝ)) * gaussianMass μ s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmoment) hC)
          (div_pos hs hmass).le
      _ = C * s + C * K * (s * s ^ (-(1/2 : ℝ))) := by field_simp [hmass.ne'] <;> ring
      _ = _ := by rw [hpow]
  have hsid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun s : ℝ => s ^ (1/2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/2)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => C * s + C * K * s ^ (1/2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hsid.const_mul C).add (hp.const_mul (C*K))
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hestimate s hs

end Preiss

#print axioms Preiss.gaussian_integral_bound_of_linear_growth
#print axioms Preiss.normalized_gaussian_integral_tendsto_zero_of_linear_growth
