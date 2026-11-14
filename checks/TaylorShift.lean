import Preiss.Analysis.AsymptoticCoefficients
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Tactic
open Filter Set Asymptotics
open scoped Topology
namespace Preiss
theorem first_second_taylor_coefficients_of_mul_scale
    (f g : ℝ → ℝ) (a b c d : ℝ)
    (hf : IsLittleO (𝓝[>] (0 : ℝ)) (fun s => f s - s * a) (fun s : ℝ => s))
    (hg : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => g s - s * b - (s ^ 2 / 2) * c) (fun s : ℝ => s ^ 2))
    (heq : ∀ᶠ s in 𝓝[>] (0 : ℝ), g s = d * s * f s) :
    b = 0 ∧ c = 2 * d * a := by
  have hprod := (hf.mul_isBigO (isBigO_refl (fun s : ℝ => s) (𝓝[>] (0 : ℝ)))).const_mul_left d
  have hga : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => g s - s ^ 2 * (d * a)) (fun s : ℝ => s ^ 2) := by
    apply hprod.congr' ?_ ?_
    · filter_upwards [heq] with s hs
      rw [hs]
      ring
    · exact Eventually.of_forall fun s => by ring
  have hpoly : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => s * b + s ^ 2 * (c / 2 - d * a)) (fun s : ℝ => s ^ 2) := by
    apply (hga.sub hg).congr' ?_ (EventuallyEq.refl _ _)
    exact Eventually.of_forall fun s => by ring
  have h21 : IsLittleO (𝓝[>] (0 : ℝ)) (fun s : ℝ => s ^ 2) (fun s : ℝ => s) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_rpow_nhdsGT_zero (a := (2 : ℝ)) (b := (1 : ℝ)) (by norm_num))
  have hlin : IsLittleO (𝓝[>] (0 : ℝ)) (fun s : ℝ => s * b) (fun s : ℝ => s) := by
    apply ((hpoly.trans_isBigO h21.isBigO).sub (h21.const_mul_left (c / 2 - d * a))).congr'
      ?_ (EventuallyEq.refl _ _)
    exact Eventually.of_forall fun s => by ring
  have hb : b = 0 := eq_zero_of_isLittleO_pow_smul 1 b
    (by simpa only [pow_one, smul_eq_mul] using hlin)
  have hc : c / 2 - d * a = 0 := eq_zero_of_isLittleO_pow_smul 2 (c / 2 - d * a)
    (by simpa only [hb, mul_zero, zero_add, smul_eq_mul] using hpoly)
  exact ⟨hb, by nlinarith⟩

#print axioms first_second_taylor_coefficients_of_mul_scale
end Preiss
