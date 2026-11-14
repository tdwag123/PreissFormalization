module
public import Preiss.Uniform.MomentForms
public import Preiss.Tangent.Blowup
public import Mathlib.Tactic.Linarith

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace Preiss
variable {n m : ℕ}

theorem gaussianMomentForm_smul (μ : Measure (Euclidean n))
    (c : ℝ≥0∞) (hc : 0 < c) (hcfin : c ≠ ∞) (k : ℕ) (s : ℝ) :
    gaussianMomentForm (c • μ) k s = gaussianMomentForm μ k s := by
  have hcr : c.toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos (ne_of_gt hc) hcfin)
  simp [gaussianMomentForm, gaussianMass, integral_smul_measure, smul_smul,
    smul_eq_mul, mul_inv_rev, mul_assoc, hcr]

theorem gaussianMomentForm_dilate {n m : ℕ} (μ : Measure (Euclidean n))
    (k : ℕ) (s r : ℝ) (hr : 0 < r) :
    gaussianMomentForm (dimensionalBlowup m μ 0 r) k s =
      (r ^ k) • gaussianMomentForm μ k (s / r ^ 2) := by
  let φ : Euclidean n → Euclidean n := fun z => r⁻¹ • z
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hweight (t : ℝ) : Continuous (fun z : Euclidean n => Real.exp (-t * ‖z‖ ^ 2)) := by fun_prop
  have hkernel (t : ℝ) : Continuous (fun z : Euclidean n =>
      Real.exp (-t * ‖z‖ ^ 2) • momentKernel k z) :=
    (hweight t).smul (continuous_momentKernel k)
  have hnorm (z : Euclidean n) : ‖φ z‖ ^ 2 = (r ^ 2)⁻¹ * ‖z‖ ^ 2 := by
    dsimp [φ]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), mul_pow, inv_pow]
  have hexp (z : Euclidean n) : Real.exp (-s * ‖φ z‖ ^ 2) =
      Real.exp (-(s / r ^ 2) * ‖z‖ ^ 2) := by
    rw [hnorm]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  have hmass : gaussianMass (μ.map φ) s = gaussianMass μ (s / r ^ 2) := by
    unfold gaussianMass
    rw [integral_map hφ.aemeasurable (hweight s).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall hexp)
  have hmoment : (∫ z, Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z ∂μ.map φ) =
      (r ^ k)⁻¹ • (∫ z, Real.exp (-(s / r ^ 2) * ‖z‖ ^ 2) • momentKernel k z ∂μ) := by
    rw [integral_map hφ.aemeasurable (hkernel s).aestronglyMeasurable, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hexp]
    change Real.exp (-(s / r ^ 2) * ‖z‖ ^ 2) • momentKernel k (r⁻¹ • z) = _
    rw [momentKernel_smul, inv_pow]
    simp only [smul_smul]
    congr 1
    ring
  have hscale : ((2 * s) ^ k / (k.factorial : ℝ)) * (r ^ k)⁻¹ =
      r ^ k * ((2 * (s / r ^ 2)) ^ k / (k.factorial : ℝ)) := by
    have hrk : r ^ k ≠ 0 := pow_ne_zero k (ne_of_gt hr)
    have hfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hpow : (r ^ 2) ^ k = (r ^ k) ^ 2 := by simp only [← pow_mul, Nat.mul_comm]
    simp only [mul_pow, div_pow, hpow]
    field_simp [hrk, hfac]
  have hmap : gaussianMomentForm (μ.map φ) k s =
      r ^ k • gaussianMomentForm μ k (s / r ^ 2) := by
    unfold gaussianMomentForm
    rw [hmass, hmoment]
    simp only [smul_smul]
    congr 1
    calc
      _ = (((2 * s) ^ k / (k.factorial : ℝ)) * (r ^ k)⁻¹) *
          (gaussianMass μ (s / r ^ 2))⁻¹ := by ring
      _ = _ := by rw [hscale]; ring
  have hc : 0 < (ENNReal.ofReal (r ^ m))⁻¹ := ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  have hcfin : (ENNReal.ofReal (r ^ m))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr m)))
  have hscalar := gaussianMomentForm_smul (μ.map φ) (ENNReal.ofReal (r ^ m))⁻¹ hc hcfin k s
  simpa only [dimensionalBlowup, sub_zero, φ] using hscalar.trans hmap


theorem gaussianMomentForm_map_linearIsometry {n d : ℕ}
    (L : Euclidean n →ₗᵢ[ℝ] Euclidean d) (μ : Measure (Euclidean n))
    (k : ℕ) (s : ℝ) (u : Fin k → Euclidean n) :
    gaussianMomentForm (μ.map L) k s (fun i => L (u i)) =
      gaussianMomentForm μ k s u := by
  let fN : Euclidean n → MomentForm n k :=
    fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z
  let fD : Euclidean d → MomentForm d k :=
    fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z
  have hcN : Continuous fN := by
    exact (show Continuous (fun z : Euclidean n => Real.exp (-s * ‖z‖ ^ 2)) by fun_prop).smul
      (continuous_momentKernel k)
  have hcD : Continuous fD := by
    exact (show Continuous (fun z : Euclidean d => Real.exp (-s * ‖z‖ ^ 2)) by fun_prop).smul
      (continuous_momentKernel k)
  have hnorm : ∀ z, ‖fD (L z)‖ = ‖fN z‖ := by
    intro z
    simp only [fD, fN, norm_smul, norm_momentKernel, L.norm_map]
  have hcomp : Integrable (fD ∘ L) μ ↔ Integrable fN μ :=
    integrable_congr' (hcD.comp L.continuous).aestronglyMeasurable hcN.aestronglyMeasurable
      (Filter.Eventually.of_forall hnorm)
  have hiff : Integrable fD (μ.map L) ↔ Integrable fN μ :=
    (integrable_map_measure hcD.aestronglyMeasurable L.continuous.measurable.aemeasurable).trans hcomp
  by_cases hint : Integrable fN μ
  · rw [gaussianMomentForm_apply _ _ _ (hiff.mpr hint), gaussianMomentForm_apply _ _ _ hint]
    have hmass : (∫ z : Euclidean d, Real.exp (-s * ‖z‖ ^ 2) ∂μ.map L) =
        ∫ z : Euclidean n, Real.exp (-s * ‖z‖ ^ 2) ∂μ := by
      have hc : Continuous (fun z : Euclidean d => Real.exp (-s * ‖z‖ ^ 2)) := by fun_prop
      rw [integral_map L.continuous.measurable.aemeasurable hc.aestronglyMeasurable]
      simp only [L.norm_map]
    have hscalar :
        (∫ z : Euclidean d, (∏ i, inner ℝ z (L (u i))) * Real.exp (-s * ‖z‖ ^ 2) ∂μ.map L) =
        ∫ z : Euclidean n, (∏ i, inner ℝ z (u i)) * Real.exp (-s * ‖z‖ ^ 2) ∂μ := by
      have hc : Continuous (fun z : Euclidean d =>
          (∏ i, inner ℝ z (L (u i))) * Real.exp (-s * ‖z‖ ^ 2)) := by fun_prop
      rw [integral_map L.continuous.measurable.aemeasurable hc.aestronglyMeasurable]
      simp only [L.inner_map_map, L.norm_map]
    unfold gaussianMoment
    rw [hmass, hscalar]
  · have hnot : ¬ Integrable fD (μ.map L) := fun h => hint (hiff.mp h)
    dsimp only [fD] at hnot
    dsimp only [fN] at hint
    simp only [gaussianMomentForm, integral_undef hnot, integral_undef hint, smul_zero,
      ContinuousMultilinearMap.zero_apply]


theorem gaussianMomentForm_eq_zero_of_odd_of_map_neg
    (μ : Measure (Euclidean n))
    (hμ : μ.map (fun z => -z) = μ) (k : ℕ) (hk : Odd k) (s : ℝ) :
    gaussianMomentForm μ k s = 0 := by
  let F : Euclidean n → MomentForm n k :=
    fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z
  have hcont : Continuous F :=
    (show Continuous (fun z : Euclidean n => Real.exp (-s * ‖z‖ ^ 2)) by fun_prop).smul
      (continuous_momentKernel k)
  have hF (z : Euclidean n) : F (-z) = -F z := by
    have hK : momentKernel k (-z) = -momentKernel k z := by
      calc
        _ = ((-1 : ℝ) ^ k) • momentKernel k z := by
          simpa only [neg_one_smul] using momentKernel_smul k z (-1)
        _ = -momentKernel k z := by
          rw [hk.neg_one_pow]
          exact neg_one_smul ℝ (momentKernel k z)
    simp only [F, norm_neg, hK, smul_neg]
  have hchange : (∫ z, F z ∂μ) = ∫ z, F (-z) ∂μ := by
    conv_lhs => rw [← hμ]
    exact integral_map measurable_neg.aemeasurable hcont.aestronglyMeasurable
  have hneg : (∫ z, F z ∂μ) = -(∫ z, F z ∂μ) := by
    calc
      _ = ∫ z, F (-z) ∂μ := hchange
      _ = _ := by simp_rw [hF]; exact integral_neg _
  have hzero : (∫ z, F z ∂μ) = 0 := by
    ext u
    have h := congrArg (fun A : MomentForm n k => A u) hneg
    simp only [ContinuousMultilinearMap.neg_apply] at h
    change (∫ z, F z ∂μ) u = 0
    linarith
  change _ • (∫ z, F z ∂μ) = 0
  rw [hzero, smul_zero]

end Preiss
