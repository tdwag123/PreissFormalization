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


theorem pow_mul_gaussian_half_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (k : ℕ) (hk : 0 < k) :
    r ^ k * Real.exp (-(s / 2) * r ^ 2) ≤ ((k : ℝ) / s) ^ ((k : ℝ) / 2) := by
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  let t := s * r ^ 2 / (k : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsmall : t * Real.exp (-t) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one t).trans (by simpa using Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have hbase : r ^ 2 * Real.exp (-t) ≤ (k : ℝ) / s := by
    apply (le_div_iff₀ hs).mpr
    have h := (mul_le_mul_of_nonneg_right hsmall hk'.le)
    dsimp [t] at h ⊢
    field_simp at h ⊢
    nlinarith
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ r ^ 2 * Real.exp (-t)) hbase
    (div_nonneg hk'.le (by norm_num : (0 : ℝ) ≤ 2))
  have heq : (r ^ 2 * Real.exp (-t)) ^ ((k : ℝ) / 2) =
      r ^ k * Real.exp (-(s / 2) * r ^ 2) := by
    have hR : (r^2)^((k : ℝ)/2) = r^k := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr]
      norm_num only [Nat.cast_ofNat]
      have hcast : (2 : ℝ) * ((k : ℝ) / 2) = k := by ring
      rw [hcast, Real.rpow_natCast]
    rw [Real.mul_rpow (sq_nonneg r) (Real.exp_pos _).le, hR, ← Real.exp_mul]
    congr 2
    dsimp [t]
    field_simp
  rwa [heq] at hpow

theorem integral_gaussian_center_parameter_of_closedBall_power
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [SFinite μ] (x : E) (C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d)
    (hball : ∀ r : ℝ, 0 < r → μ (closedBall x r) = ENNReal.ofReal (C * r ^ d))
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z - x‖ ^ 2)) μ ∧
      (∫ z, Real.exp (-s * ‖z - x‖ ^ 2) ∂μ) =
        Real.Gamma (d / 2 + 1) * C * s ^ (-(d / 2)) := by
  let φ : E → E := fun z => z - x
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hball' (r : ℝ) (hr : 0 < r) :
      μ.map φ (closedBall 0 r) = ENNReal.ofReal (C * r ^ d) := by
    rw [Measure.map_apply hφ measurableSet_closedBall]
    have hset : φ ⁻¹' closedBall 0 r = closedBall x r := by
      ext z
      simp only [mem_preimage, mem_closedBall, dist_zero_right, dist_eq_norm, φ, sub_zero]
    rw [hset, hball r hr]
  obtain ⟨hint,hval⟩ := integral_gaussian_parameter_of_closedBall_power (μ.map φ) C d hC hd hball' s hs
  have hf : Continuous (fun z : E => Real.exp (-s * ‖z‖ ^ 2)) := by fun_prop
  have hint' := (integrable_map_measure hf.aestronglyMeasurable hφ.aemeasurable).mp hint
  rw [integral_map hφ.aemeasurable hf.aestronglyMeasurable] at hval
  exact ⟨hint',hval⟩


end Preiss
