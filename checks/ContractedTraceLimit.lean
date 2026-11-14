import Preiss.Analysis.ScaleDerivative
import Preiss.Analysis.NormalizedIntegral
import Preiss.Analysis.TaylorLimits
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Preiss.Uniform.MomentTrace
import Mathlib.Analysis.Calculus.Deriv.Inv
import Preiss.Uniform.FlatAtInfinity.TraceLimits
import Preiss.Uniform.MomentExpansion
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}


theorem hasDerivAt_normalized_polynomial_gaussian_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (P : MvPolynomial (Fin n) ℝ) (s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun t => (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-t * ‖z‖^2) ∂μ) /
        gaussianMass μ t)
      (((m : ℝ) / (2*s)) *
          ((∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖^2) ∂μ) /
            gaussianMass μ s) -
        (∫ z, ‖z‖^2 * MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖^2) ∂μ) /
          gaussianMass μ s) s := by
  have hg := IsUnitUniform.hasPolynomialGrowthBound μ hμ
  have hN := hasDerivAt_integral_polynomial_gaussian_of_ball_bound μ 1 (m : ℝ)
    hg.1 hg.2.2 P s hs
  have hI : HasDerivAt (gaussianMass μ)
      (-((m : ℝ) / (2*s)) * gaussianMass μ s) s := by
    have h := hasDerivAt_integral_polynomial_gaussian_of_ball_bound μ 1 (m : ℝ)
      hg.1 hg.2.2 (1 : MvPolynomial (Fin n) ℝ) s hs
    simp only [map_one, mul_one, one_mul] at h
    rw [integral_norm_sq_gaussian_unitUniform μ hm hμ s hs] at h
    have heq : (fun t : ℝ => ∫ z, Real.exp (-t * ‖z‖^2) ∂μ) = gaussianMass μ := rfl
    rw [← heq]
    simpa only [gaussianMass, neg_mul] using h
  have hmass : gaussianMass μ s ≠ 0 := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)).ne'
  convert! hN.div hI hmass using 1
  field_simp [hmass, hs.ne']
  <;> ring

theorem hasDerivAt_normalized_centered_gaussian_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (b w : Euclidean n) (s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun t => (∫ z, inner ℝ (z-b) w * Real.exp (-t * ‖z‖^2) ∂μ) / gaussianMass μ t)
      (((m : ℝ) / (2*s)) *
          ((∫ z, inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ) / gaussianMass μ s) -
        (∫ z, ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ) /
          gaussianMass μ s) s := by
  let P : MvPolynomial (Fin n) ℝ :=
    (∑ j : Fin n, MvPolynomial.C (w j) * MvPolynomial.X j) - MvPolynomial.C (inner ℝ b w)
  have heval (z : Euclidean n) : MvPolynomial.eval (fun j => z j) P = inner ℝ (z-b) w := by
    rw [inner_sub_left]
    change MvPolynomial.eval (fun j => z j) P = (∑ j : Fin n, w j * z j) - inner ℝ b w
    simp [P]
  simpa only [heval] using hasDerivAt_normalized_polynomial_gaussian_unitUniform μ hm hμ P s hs








theorem exists_normalized_norm_sq_centered_gaussian_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B) (b w : Euclidean n) :
    ∃ L : ℝ, Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let A (i : Fin n) := 3 * B 3 2 ![e i,e i,w] - 4 * B 2 1 ![e i,e i] * inner ℝ b w
  have hlim := tendsto_finset_sum Finset.univ (fun i _ =>
    mixed_gaussian_limit_of_moment_expansion μ hm hμ B hB b (e i) w)
  refine ⟨(∑ i, A i) / 8, ?_⟩
  apply (hlim.div_const 8).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  have hint (i : Fin n) : Integrable
      (fun z => Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2 * inner ℝ (z-b) w) μ := by
    have h₃ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Euclidean n) ℝ
      ![e i,e i,w]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 3 s hs')
    have h₂ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
      ![e i,e i]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 2 s hs')
    have hi₃ : Integrable (fun z => Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2 * inner ℝ z w) μ := by
      simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
        Fin.prod_univ_three, pow_two, mul_assoc] using h₃
    have hi₂ : Integrable (fun z => Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2) μ := by
      simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
        Fin.prod_univ_two, pow_two, mul_assoc] using h₂
    apply (hi₃.sub (hi₂.mul_const (inner ℝ b w))).congr
    exact Eventually.of_forall fun z => by simp only [Pi.sub_apply, inner_sub_left, mul_sub]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hint i)]
  have hsum (z : Euclidean n) :
      (∑ i, Real.exp (-s * ‖z‖^2) * (inner ℝ z (e i))^2 * inner ℝ (z-b) w) =
        ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, e.sum_sq_inner_left z]
    ring
  simp_rw [hsum]
  ring

theorem normalized_norm_sq_centered_gaussian_limit_eq_zero
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (b w : Euclidean n) (hb : B 1 1 (fun _ => w) = 2 * inner ℝ b w) :
    Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨L,hL⟩ := exists_normalized_norm_sq_centered_gaussian_limit μ hm hμ B hB b w
  let f : ℝ → ℝ := fun s =>
    (∫ z, inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ) / gaussianMass μ s
  let f' : ℝ → ℝ := fun s => ((m : ℝ) / (2*s)) * f s -
    (∫ z, ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ) / gaussianMass μ s
  have hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    normalized_centered_gaussian_limit_of_first_coefficient μ hm hμ B hB b w hb
  have hd : ∀ᶠ s in 𝓝[>] (0 : ℝ), HasDerivAt f (f' s) s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hasDerivAt_normalized_centered_gaussian_unitUniform μ hm hμ b w s hs
  have hder : Tendsto (fun s => s * f' s) (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    have h := (hf.const_mul ((m : ℝ)/2)).sub hL
    simp only [mul_zero, zero_sub] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    dsimp only [f']
    have hmass : gaussianMass μ s ≠ 0 := by
      rw [gaussianMass_unitUniform μ hm hμ s hs]
      exact (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)).ne'
    field_simp [hs'.ne', hmass]
    <;> ring
  have hzero := scale_derivative_limit_eq_zero f f' 0 (-L) hd hf hder
  have hLzero : L = 0 := neg_eq_zero.mp hzero
  simpa only [hLzero] using hL

theorem contracted_gaussian_limit_eq_zero_of_bounded_tube
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (K : Submodule ℝ (Euclidean n)) (b : Euclidean n) (w : Kᗮ)
    (hb : B 1 1 (fun _ => (w : Euclidean n)) = 2 * inner ℝ b (w : Euclidean n))
    (R : ℝ) (hR : 0 ≤ R) (htube : ∀ z ∈ μ.support, ‖z - K.starProjection z‖ ≤ R) :
    Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s * ‖z‖^2) * ‖K.starProjection z‖^2 * inner ℝ (z-b) (w : Euclidean n) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let Q : Euclidean n →L[ℝ] Euclidean n := ContinuousLinearMap.id ℝ _ - K.starProjection
  have hQeq (z : Euclidean n) : Q z = z - K.starProjection z := rfl
  let F : Euclidean n → ℝ := fun z => ‖Q z‖^2 * inner ℝ (z-b) (w : Euclidean n)
  let C : ℝ := R^2 * ((R + ‖b‖) * ‖w‖)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᵐ z ∂μ, ‖F z‖ ≤ C := by
    filter_upwards [μ.support_mem_ae] with z hz
    have hQ : ‖Q z‖ ≤ R := htube z hz
    have hP : inner ℝ (K.starProjection z) (w : Euclidean n) = 0 :=
      K.inner_right_of_mem_orthogonal (K.orthogonalProjectionOnto z).property w.property
    have hinner : inner ℝ (z-b) (w : Euclidean n) = inner ℝ (Q z-b) (w : Euclidean n) := by
      rw [hQeq]
      simp only [inner_sub_left, hP, sub_zero]
    have hn : ‖Q z-b‖ ≤ R + ‖b‖ := (norm_sub_le _ _).trans (add_le_add hQ (le_refl ‖b‖))
    have hi : ‖inner ℝ (z-b) (w : Euclidean n)‖ ≤ (R+‖b‖)*‖w‖ := by
      rw [hinner, Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    dsimp only [F, C]
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hQ 2) hi
      (norm_nonneg _) (sq_nonneg R)
  have hint (s : ℝ) (hs : 0 < s) : Integrable (fun z : Euclidean n => Real.exp (-s*‖z‖^2)) μ := by
    simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_gaussian_of_polynomial_growth
      μ hμ.1 1 (m : ℝ) (IsUnitUniform.hasPolynomialGrowthBound μ hμ) 0 s hs
  have hmass (s : ℝ) (hs : 0 < s) : 0 < gaussianMass μ s := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)
  have herror := tendsto_scale_normalized_integral_of_ae_bound μ
    (fun s z => Real.exp (-s*‖z‖^2)) F C
    (fun s hs => Eventually.of_forall fun z => (Real.exp_pos _).le) hint hmass hbound
  have hfull := normalized_norm_sq_centered_gaussian_limit_eq_zero μ hm hμ B hB b w hb
  have h := hfull.sub herror
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  let P : MvPolynomial (Fin n) ℝ :=
    (∑ j : Fin n, MvPolynomial.C (w.val j) * MvPolynomial.X j) -
      MvPolynomial.C (inner ℝ b (w : Euclidean n))
  have heval (z : Euclidean n) : MvPolynomial.eval (fun j => z j) P = inner ℝ (z-b) (w : Euclidean n) := by
    rw [inner_sub_left]
    change MvPolynomial.eval (fun j => z j) P =
      (∑ j : Fin n, w.val j * z j) - inner ℝ b (w : Euclidean n)
    simp [P]
  have hiFull : Integrable
      (fun z => ‖z‖^2 * inner ℝ (z-b) (w : Euclidean n) * Real.exp (-s*‖z‖^2)) μ := by
    simpa only [heval] using integrable_norm_pow_mul_polynomial_mul_gaussian μ 1 (m : ℝ)
      (by positivity) (IsUnitUniform.hasPolynomialGrowthBound μ hμ).2.2 P 2 s hs'
  have hiErr : Integrable (fun z => Real.exp (-s*‖z‖^2) * F z) μ := by
    apply ((hint s hs').const_mul C).mono'
    · exact (show Continuous (fun z => Real.exp (-s*‖z‖^2) * F z) by
        dsimp [F]; fun_prop).aestronglyMeasurable
    · filter_upwards [hbound] with z hz
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  change (s / gaussianMass μ s) * _ - (s / gaussianMass μ s) * _ = _
  rw [← mul_sub, ← integral_sub hiFull hiErr]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection z K
    rw [K.starProjection_orthogonal_val] at hpyth
    dsimp only [F]
    rw [hQeq, hpyth]
    ring

#print axioms normalized_norm_sq_centered_gaussian_limit_eq_zero
#print axioms contracted_gaussian_limit_eq_zero_of_bounded_tube


theorem contracted_gaussian_limit_eq_zero_proved
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b) (w : V.1ᗮ) :
    Tendsto (fun s : ℝ => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * ‖proj V z‖ ^ 2 *
        inner ℝ (z - (b : Euclidean n)) (w : Euclidean n) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact contracted_gaussian_limit_eq_zero_of_bounded_tube μ hm hμ B hB V.1 b w (hb w)
    (2*‖b‖) (by positivity) (fun z hz =>
      (support_normal_sq_eq_inner μ hm hμ B hB V hV b hb z hz).2.2)

#print axioms contracted_gaussian_limit_eq_zero_proved
end Preiss
