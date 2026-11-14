module
public import Preiss.Uniform.GaussianNormBounds
public import Preiss.Uniform.MomentCoefficientEstimates
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

@[expose] public section
namespace Preiss
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators
variable {n m : ℕ}

theorem gaussianMomentForm_apply_isBigO_of_product_bound
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (k d : ℕ) (u : Fin k → Euclidean n) (C : ℝ) (hC : 0 ≤ C)
    (hprod : ∀ᵐ z ∂μ, |∏ i, inner ℝ z (u i)| ≤ C * ‖z‖^d) :
    IsBigO (𝓝[>] (0 : ℝ)) (fun s => gaussianMomentForm μ k s u)
      (fun s : ℝ => s^((k : ℝ)-(d : ℝ)/2)) := by
  have hmass (s : ℝ) (hs : 0 < s) : 0 < gaussianMass μ s := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)
  obtain ⟨D, hD, hnorm⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, 0 < s →
      (∫ z, ‖z‖^d * Real.exp (-s*‖z‖^2) ∂μ) / gaussianMass μ s ≤
        D * s^(-((d : ℝ)/2)) := by
    by_cases hd : d = 0
    · subst d
      refine ⟨1, zero_le_one, fun s hs => ?_⟩
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, neg_zero, Real.rpow_zero]
      change gaussianMass μ s / gaussianMass μ s ≤ 1
      exact (div_self (hmass s hs).ne').le
    · refine ⟨(2 : ℝ)^((m : ℝ)/2) * (d : ℝ)^((d : ℝ)/2), by positivity, ?_⟩
      intro s hs
      exact normalized_gaussian_norm_pow_le_unitUniform μ hm hμ d
        (Nat.pos_of_ne_zero hd) s hs
  apply IsBigO.of_bound ((2 : ℝ)^k / (k.factorial : ℝ) * C * D)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hgrowth := IsUnitUniform.hasPolynomialGrowthBound μ hμ
  have hintd := integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ.1
    1 (m : ℝ) hgrowth d s hspos
  have hIntegral : ‖∫ z, (∏ i, inner ℝ z (u i)) * Real.exp (-s*‖z‖^2) ∂μ‖ ≤
      C * ∫ z, ‖z‖^d * Real.exp (-s*‖z‖^2) ∂μ := by
    calc
      _ ≤ ∫ z, ‖(∏ i, inner ℝ z (u i)) * Real.exp (-s*‖z‖^2)‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ z, C * (‖z‖^d * Real.exp (-s*‖z‖^2)) ∂μ := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (hintd.const_mul C)
        filter_upwards [hprod] with z hz
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc]
          using mul_le_mul_of_nonneg_right hz (Real.exp_pos (-s*‖z‖^2)).le
      _ = _ := integral_const_mul _ _
  have hcoef : 0 ≤ (2*s)^k / (k.factorial : ℝ) * (gaussianMass μ s)⁻¹ := by
    have hf : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hM := hmass s hspos
    positivity
  have hbound : ‖gaussianMomentForm μ k s u‖ ≤
      ((2*s)^k / (k.factorial : ℝ) * (gaussianMass μ s)⁻¹) *
        (C * ∫ z, ‖z‖^d * Real.exp (-s*‖z‖^2) ∂μ) := by
    rw [gaussianMomentForm_apply μ k s (integrable_gaussianMomentKernel μ hm hμ k s hspos)]
    unfold gaussianMoment
    change ‖((2*s)^k / (k.factorial : ℝ) * (gaussianMass μ s)⁻¹) *
      (∫ z, (∏ i, inner ℝ z (u i)) * Real.exp (-s*‖z‖^2) ∂μ)‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left hIntegral hcoef
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hspos.le _)]
  calc
    _ ≤ ((2*s)^k / (k.factorial : ℝ) * (gaussianMass μ s)⁻¹) *
        (C * ∫ z, ‖z‖^d * Real.exp (-s*‖z‖^2) ∂μ) := hbound
    _ = ((2*s)^k / (k.factorial : ℝ) * C) *
        ((∫ z, ‖z‖^d * Real.exp (-s*‖z‖^2) ∂μ) / gaussianMass μ s) := by ring
    _ ≤ ((2*s)^k / (k.factorial : ℝ) * C) * (D * s^(-((d : ℝ)/2))) :=
      mul_le_mul_of_nonneg_left (hnorm s hspos) (by positivity)
    _ = ((2 : ℝ)^k / (k.factorial : ℝ) * C * D) *
        (s^(k : ℝ) * s^(-((d : ℝ)/2))) := by rw [Real.rpow_natCast, mul_pow]; ring
    _ = _ := by rw [← Real.rpow_add hspos]; congr 2 <;> ring

theorem thirdMomentCoefficient_two_normal_eq_zero_of_bounded_tube
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (K : Submodule ℝ (Euclidean n)) (R : ℝ) (hR : 0 ≤ R)
    (hsupport : ∀ z ∈ μ.support, ‖z - K.starProjection z‖ ≤ R)
    (v : Euclidean n) (w : Kᗮ) : B 3 2 ![v, (w : Euclidean n), (w : Euclidean n)] = 0 := by
  have hw (z : Euclidean n) (hz : z ∈ μ.support) :
      |inner ℝ z (w : Euclidean n)| ≤ R * ‖w‖ := by
    have hzero : inner ℝ (K.starProjection z) (w : Euclidean n) = 0 :=
      K.inner_right_of_mem_orthogonal (K.orthogonalProjectionOnto z).property w.property
    have heq : inner ℝ z (w : Euclidean n) =
        inner ℝ (z - K.starProjection z) (w : Euclidean n) := by
      rw [inner_sub_left, hzero, sub_zero]
    rw [heq]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hsupport z hz) (norm_nonneg _))
  have hprod : ∀ᵐ z ∂μ,
      |∏ i : Fin 3, inner ℝ z (![v, (w : Euclidean n), (w : Euclidean n)] i)| ≤
        (‖v‖ * (R * ‖w‖)^2) * ‖z‖^1 := by
    filter_upwards [μ.support_mem_ae] with z hz
    calc
      _ = |inner ℝ z v| * |inner ℝ z (w : Euclidean n)|^2 := by
        simp [Fin.prod_univ_three, abs_mul, pow_two, mul_assoc]
      _ ≤ (‖z‖ * ‖v‖) * (R * ‖w‖)^2 := by
        gcongr
        · exact abs_real_inner_le_norm z v
        · exact hw z hz
      _ = _ := by ring
  have hbound := gaussianMomentForm_apply_isBigO_of_product_bound μ hm hμ 3 1
    ![v, (w : Euclidean n), (w : Euclidean n)] (‖v‖ * (R * ‖w‖)^2)
    (by positivity) hprod
  exact gaussianMomentCoefficient_apply_eq_zero_of_lt_growth μ B hB 3 (by decide)
    ![v, (w : Euclidean n), (w : Euclidean n)] hbound 2 (by decide) (by norm_num)

end Preiss
