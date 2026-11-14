module
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Map

/-! # Measure support under transport and nonzero scalar multiplication -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace Preiss

theorem measure_support_map_homeomorph
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : Measure X) :
    (μ.map e).support = e '' μ.support := by
  have hmem (x : Y) : x ∈ (μ.map e).support ↔ e.symm x ∈ μ.support := by
    simp only [Measure.support_eq_forall_isOpen, Set.mem_ofPred_eq]
    constructor
    · intro h U hxU hU
      have hpos := h (e '' U) ⟨e.symm x, hxU, e.apply_symm_apply x⟩ (e.isOpenMap U hU)
      rw [Measure.map_apply e.continuous.measurable (e.isOpenMap U hU).measurableSet] at hpos
      simpa only [e.injective.preimage_image] using hpos
    · intro h U hxU hU
      rw [Measure.map_apply e.continuous.measurable hU.measurableSet]
      exact h (e ⁻¹' U) (by simpa only [mem_preimage, e.apply_symm_apply] using hxU)
        (hU.preimage e.continuous)
  ext x
  rw [hmem]
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [e.symm_apply_apply] using hy

theorem measure_support_smul {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) {c : ℝ≥0∞} (hc : c ≠ 0) :
    (c • μ).support = μ.support := by
  ext x
  simp only [Measure.mem_support_iff_forall, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_pos_iff, pos_iff_ne_zero.mpr hc, true_and]

end Preiss
