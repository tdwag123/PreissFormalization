module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace Preiss
theorem gaussian_integral_bound_of_linear_growth
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (f : E → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ z ∂μ, |f z| ≤ C * (1 + ‖z‖))
    (s : ℝ)
    (h0 : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2)) μ)
    (h1 : Integrable (fun z => ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) μ) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) * f z) μ ∧
      |∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ| ≤
        C * ((∫ z, Real.exp (-s * ‖z‖ ^ 2) ∂μ) +
          ∫ z, ‖z‖ * Real.exp (-s * ‖z‖ ^ 2) ∂μ) := by
  have hdom := (h0.add h1).const_mul C
  have hnorm : ∀ᵐ z ∂μ, ‖Real.exp (-s * ‖z‖ ^ 2) * f z‖ ≤
      C * (Real.exp (-s * ‖z‖ ^ 2) + ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) := by
    filter_upwards [hbound] with z hz
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    calc
      Real.exp (-s * ‖z‖ ^ 2) * |f z| ≤
          Real.exp (-s * ‖z‖ ^ 2) * (C * (1 + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
      _ = _ := by ring
  have hmeas : Measurable (fun z : E => Real.exp (-s * ‖z‖ ^ 2) * f z) := by
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).measurable.mul hf
  have hint := hdom.mono' hmeas.aestronglyMeasurable hnorm
  refine ⟨hint, ?_⟩
  calc
    |∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ| =
        ‖∫ z, Real.exp (-s * ‖z‖ ^ 2) * f z ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ‖Real.exp (-s * ‖z‖ ^ 2) * f z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, C * (Real.exp (-s * ‖z‖ ^ 2) + ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) ∂μ :=
      integral_mono_ae hint.norm hdom hnorm
    _ = _ := by rw [integral_const_mul, integral_add h0 h1]

end Preiss
