module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-! # Normalized weighted integrals of bounded functions. -/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace Preiss

theorem tendsto_scale_normalized_integral_of_ae_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : ℝ → X → ℝ) (f : X → ℝ) (C : ℝ)
    (hw : ∀ s > 0, ∀ᵐ z ∂μ, 0 ≤ w s z)
    (hint : ∀ s > 0, Integrable (w s) μ)
    (hmass : ∀ s > 0, 0 < ∫ z, w s z ∂μ)
    (hbound : ∀ᵐ z ∂μ, ‖f z‖ ≤ C) :
    Tendsto (fun s => (s / (∫ z, w s z ∂μ)) * ∫ z, w s z * f z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun s : ℝ => s * C) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    have hi : ‖∫ z, w s z * f z ∂μ‖ ≤ C * ∫ z, w s z ∂μ := by
      calc
        _ ≤ ∫ z, C * w s z ∂μ := norm_integral_le_of_norm_le ((hint s hs').const_mul C) (by
          filter_upwards [hw s hs', hbound] with z hz hb
          rw [norm_mul, Real.norm_of_nonneg hz]
          exact (mul_le_mul_of_nonneg_left hb hz).trans_eq (mul_comm _ _))
        _ = _ := integral_const_mul _ _
    rw [norm_mul, Real.norm_of_nonneg (div_nonneg hs'.le (hmass s hs').le)]
    calc
      _ ≤ (s / (∫ z, w s z ∂μ)) * (C * ∫ z, w s z ∂μ) :=
        mul_le_mul_of_nonneg_left hi (div_nonneg hs'.le (hmass s hs').le)
      _ = s * C := by field_simp [(hmass s hs').ne']
  · have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using hid.mul_const C

end Preiss
