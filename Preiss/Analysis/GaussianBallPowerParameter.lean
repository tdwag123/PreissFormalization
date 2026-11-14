module
public import Preiss.Analysis.GaussianBallPower
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Gaussian integrals at arbitrary positive scales

A centered ball power law determines the Gaussian mass at every positive parameter.
The ambient space is an arbitrary real normed space with its Borel measurable structure.
-/

@[expose] public section
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace Preiss

theorem integral_gaussian_parameter_of_closedBall_power
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [SFinite μ] (C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d)
    (hball : ∀ r : ℝ, 0 < r → μ (closedBall 0 r) = ENNReal.ofReal (C * r ^ d))
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2)) μ ∧
      (∫ z, Real.exp (-s * ‖z‖ ^ 2) ∂μ) =
        Real.Gamma (d / 2 + 1) * C * s ^ (-(d / 2)) := by
  let a := Real.sqrt s
  have ha : 0 < a := Real.sqrt_pos.mpr hs
  let φ : E → E := fun z => a • z
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hC' : 0 ≤ C * s ^ (-(d / 2)) := mul_nonneg hC (Real.rpow_nonneg hs.le _)
  have hball' (r : ℝ) (hr : 0 < r) :
      μ.map φ (closedBall 0 r) = ENNReal.ofReal ((C * s ^ (-(d / 2))) * r ^ d) := by
    rw [Measure.map_apply hφ measurableSet_closedBall]
    have hset : φ ⁻¹' closedBall 0 r = closedBall 0 (r / a) := by
      ext z
      simp only [Set.mem_preimage, mem_closedBall, dist_zero_right, φ, norm_smul,
        Real.norm_of_nonneg ha.le]
      rw [le_div_iff₀ ha, mul_comm ‖z‖ a]
    rw [hset, hball (r/a) (div_pos hr ha)]
    congr 1
    have hpow : a ^ d = s ^ (d / 2) := by
      dsimp [a]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
      congr 1
      ring
    rw [Real.div_rpow hr.le ha.le, hpow, Real.rpow_neg hs.le]
    ring
  obtain ⟨hint,hval⟩ := integral_gaussian_of_closedBall_power (μ.map φ)
    (C * s ^ (-(d/2))) d hC' hd hball'
  have hnorm (z : E) : ‖φ z‖ ^ 2 = s * ‖z‖ ^ 2 := by
    simp only [φ, norm_smul, Real.norm_of_nonneg ha.le, mul_pow]
    rw [show a ^ 2 = s from Real.sq_sqrt hs.le]
  have heq (z : E) : Real.exp (-‖φ z‖ ^ 2) = Real.exp (-s * ‖z‖ ^ 2) := by
    rw [hnorm, neg_mul]
  have hf : Continuous (fun z : E => Real.exp (-‖z‖ ^ 2)) := by fun_prop
  have hint' := (integrable_map_measure hf.aestronglyMeasurable hφ.aemeasurable).mp hint
  have hint'' : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2)) μ := by
    simpa only [Function.comp_def, heq] using hint'
  rw [integral_map hφ.aemeasurable hf.aestronglyMeasurable] at hval
  simp_rw [heq] at hval
  exact ⟨hint'',hval.trans (by ring)⟩


end Preiss
