import FormalizingGMT.WeakConvergence.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic.Push

/-! # Nonzero limits of scalar-rescaled measures -/

open MeasureTheory Filter Topology
open scoped ENNReal CompactlySupported
namespace Preiss

theorem exists_pos_smul_of_vague_and_scaled_vague
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) (ν ξ : Measure X)
    (hν : ν.Regular) (hξ : ξ.Regular) (hν0 : ν ≠ 0) (hξ0 : ξ ≠ 0)
    (c : ℕ → ℝ≥0∞) (hlim : Measure.WeaklyConverges μ ν)
    (hscaled : Measure.WeaklyConverges (fun i => c i • μ i) ξ) :
    ∃ a : ℝ≥0∞, 0 < a ∧ a < ∞ ∧ ξ = a • ν := by
  classical
  haveI : ν.Regular := hν
  haveI : ξ.Regular := hξ
  obtain ⟨f, hf⟩ : ∃ f : C_c(X, ℝ), (∫ x, f x ∂ν) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hν0
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    simpa using h f
  let a : ℝ := (∫ x, f x ∂ξ) / (∫ x, f x ∂ν)
  have hcoef : Tendsto (fun i => (c i).toReal) atTop (𝓝 a) := by
    have hevent : ∀ᶠ i in atTop, (∫ x, f x ∂μ i) ≠ 0 :=
      (hlim f).eventually_ne hf
    have hdiv := (hscaled f).div (hlim f) hf
    apply hdiv.congr'
    filter_upwards [hevent] with i hi
    simp [integral_smul_measure, smul_eq_mul, hi]
  have ha : 0 ≤ a := ge_of_tendsto' hcoef (fun i => ENNReal.toReal_nonneg)
  haveI : (ENNReal.ofReal a • ν).Regular := Measure.Regular.smul ENNReal.ofReal_ne_top
  have heq : ξ = ENNReal.ofReal a • ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    have hmul := hcoef.mul (hlim g)
    have hleft := hscaled g
    simp only [integral_smul_measure, smul_eq_mul] at hleft ⊢
    rw [ENNReal.toReal_ofReal ha]
    exact tendsto_nhds_unique hleft hmul
  have hapos : 0 < a := lt_of_le_of_ne ha (by
    intro hzero
    apply hξ0
    simpa [← hzero] using heq)
  exact ⟨ENNReal.ofReal a, ENNReal.ofReal_pos.mpr hapos, ENNReal.ofReal_lt_top, heq⟩

end Preiss
