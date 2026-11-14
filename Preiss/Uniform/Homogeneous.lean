module

public import Preiss.Uniform.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Homogeneous integrals for conical measures

The degree may be any real number. This scaling identity needs no positivity or
integrability hypothesis: Bochner integrals on both sides use the same convention
when the integrand is not integrable.
-/

@[expose] public section
open MeasureTheory Metric Set
namespace Preiss
variable {n m : ℕ}

theorem integrableOn_homogeneous_closedBall
    (μ : Measure (Euclidean n)) (hcone : IsConical m μ)
    (h : Euclidean n → ℝ) (hh : Measurable h) (a : ℝ)
    (hhom : ∀ r > 0, ∀ z, h (r • z) = r ^ a * h z)
    (hint : IntegrableOn h (closedBall 0 1) μ) (r : ℝ) (hr : 0 < r) :
    IntegrableOn h (closedBall 0 r) μ := by
  have hscale : μ = ENNReal.ofReal (r ^ m) • μ.map (fun z => r • z) := by
    simpa only [dimensionalBlowup, sub_zero, inv_pow,
      ENNReal.ofReal_inv_of_pos (pow_pos hr m), inv_inv] using
      (hcone r⁻¹ (inv_pos.mpr hr)).symm
  have hg : Measurable (fun z : Euclidean n => r • z) :=
    (continuous_id.const_smul r).measurable
  have hpre : (fun z : Euclidean n => r • z) ⁻¹' closedBall 0 r = closedBall 0 1 := by
    ext z
    simp only [mem_preimage, mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using
      (mul_le_mul_iff_right₀ hr : r * ‖z‖ ≤ r * 1 ↔ ‖z‖ ≤ 1)
  have hrestrict : μ.restrict (closedBall 0 r) = ENNReal.ofReal (r ^ m) •
      (μ.restrict (closedBall 0 1)).map (fun z => r • z) := by
    calc
      _ = (ENNReal.ofReal (r ^ m) • μ.map (fun z => r • z)).restrict (closedBall 0 r) :=
        congrArg (fun ν => ν.restrict (closedBall 0 r)) hscale
      _ = _ := by
        rw [Measure.restrict_smul, Measure.restrict_map hg measurableSet_closedBall, hpre]
  change Integrable h (μ.restrict (closedBall 0 r))
  rw [hrestrict]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_map_measure hh.aestronglyMeasurable hg.aemeasurable).mpr
  have hunit : Integrable h (μ.restrict (closedBall 0 1)) := hint
  simpa only [Function.comp_def, hhom r hr] using hunit.const_mul (r ^ a)

theorem integral_homogeneous_closedBall
    (μ : Measure (Euclidean n)) (hcone : IsConical m μ)
    (h : Euclidean n → ℝ) (hh : Measurable h) (a : ℝ)
    (hhom : ∀ r > 0, ∀ z, h (r • z) = r ^ a * h z)
    (r : ℝ) (hr : 0 < r) :
    (∫ z in closedBall 0 r, h z ∂μ) =
      r ^ ((m : ℝ) + a) * ∫ z in closedBall 0 1, h z ∂μ := by
  have hscale : μ = ENNReal.ofReal (r ^ m) • μ.map (fun z => r • z) := by
    simpa only [dimensionalBlowup, sub_zero, inv_pow,
      ENNReal.ofReal_inv_of_pos (pow_pos hr m), inv_inv] using
      (hcone r⁻¹ (inv_pos.mpr hr)).symm
  have hpre : (fun z : Euclidean n => r • z) ⁻¹' closedBall 0 r = closedBall 0 1 := by
    ext z
    simp only [mem_preimage, mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using
      (mul_le_mul_iff_right₀ hr : r * ‖z‖ ≤ r * 1 ↔ ‖z‖ ≤ 1)
  have hmap : (∫ z in closedBall 0 r, h z ∂μ.map (fun z => r • z)) =
      ∫ z in closedBall 0 1, h (r • z) ∂μ := by
    have hf : AEStronglyMeasurable h (μ.map (fun z => r • z)) :=
      hh.aestronglyMeasurable
    have hg : Measurable (fun z : Euclidean n => r • z) :=
      (continuous_id.const_smul r).measurable
    rw [setIntegral_map measurableSet_closedBall hf hg.aemeasurable, hpre]
  calc
    (∫ z in closedBall 0 r, h z ∂μ) =
        ∫ z in closedBall 0 r, h z ∂(ENNReal.ofReal (r ^ m) •
          μ.map (fun z => r • z)) := congrArg (fun ν => ∫ z in closedBall 0 r, h z ∂ν) hscale
    _ = r ^ m * ∫ z in closedBall 0 r, h z ∂μ.map (fun z => r • z) := by
      rw [Measure.restrict_smul, integral_smul_measure,
        ENNReal.toReal_ofReal (pow_nonneg hr.le m), smul_eq_mul]
    _ = r ^ m * ∫ z in closedBall 0 1, h (r • z) ∂μ := congrArg (fun t => r ^ m * t) hmap
    _ = r ^ m * (r ^ a * ∫ z in closedBall 0 1, h z ∂μ) := by
      simp_rw [hhom r hr]
      rw [integral_const_mul]
    _ = r ^ ((m : ℝ) + a) * ∫ z in closedBall 0 1, h z ∂μ := by
      rw [Real.rpow_add hr, Real.rpow_natCast, mul_assoc]

end Preiss
