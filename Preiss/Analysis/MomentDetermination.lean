module
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
/-! # Determination by moments with all exponential moments

The hypotheses make each complex moment generating function entire. Its derivatives
at zero are the moments, so analytic uniqueness determines the function.
-/

namespace Preiss

theorem complexMGF_eq_of_all_moments_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hX : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ)
    (hY : ∀ t : ℝ, Integrable (fun y => Real.exp (t * Y y)) ν)
    (hmom : ∀ k : ℕ, (∫ x, X x ^ k ∂μ) = ∫ y, Y y ^ k ∂ν) :
    complexMGF X μ = complexMGF Y ν := by
  have hsetX : integrableExpSet X μ = univ := eq_univ_of_forall hX
  have hsetY : integrableExpSet Y ν = univ := eq_univ_of_forall hY
  have hAX : AnalyticOnNhd ℂ (complexMGF X μ) univ := by
    simpa only [hsetX, interior_univ, mem_univ, setOf_true] using
      (analyticOnNhd_complexMGF (X := X) (μ := μ))
  have hAY : AnalyticOnNhd ℂ (complexMGF Y ν) univ := by
    simpa only [hsetY, interior_univ, mem_univ, setOf_true] using
      (analyticOnNhd_complexMGF (X := Y) (μ := ν))
  have hx0 : (0 : ℂ).re ∈ interior (integrableExpSet X μ) := by simp [hsetX]
  have hy0 : (0 : ℂ).re ∈ interior (integrableExpSet Y ν) := by simp [hsetY]
  have hderiv (k : ℕ) :
      iteratedDeriv k (complexMGF X μ) 0 = iteratedDeriv k (complexMGF Y ν) 0 := by
    rw [iteratedDeriv_complexMGF hx0, iteratedDeriv_complexMGF hy0]
    simp only [zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow,
      integral_complex_ofReal, hmom]
  have hcoeff :
      FormalMultilinearSeries.ofScalars ℂ
        (fun k => iteratedDeriv k (complexMGF X μ) 0 / (k.factorial : ℂ)) =
      FormalMultilinearSeries.ofScalars ℂ
        (fun k => iteratedDeriv k (complexMGF Y ν) 0 / (k.factorial : ℂ)) := by
    congr 1
    funext k
    rw [hderiv]
  have hseriesX := (hAX 0 (mem_univ _)).hasFPowerSeriesAt
  have hseriesY := (hAY 0 (mem_univ _)).hasFPowerSeriesAt
  rw [hcoeff] at hseriesX
  have hzero : HasFPowerSeriesAt (complexMGF X μ - complexMGF Y ν)
      (0 : FormalMultilinearSeries ℂ ℂ ℂ) 0 := by
    simpa only [sub_self] using hseriesX.sub hseriesY
  have heq : complexMGF X μ =ᶠ[𝓝 (0 : ℂ)] complexMGF Y ν := by
    filter_upwards [hzero.eventually_eq_zero] with z hz
    exact sub_eq_zero.mp (by simpa only [Pi.sub_apply] using hz)
  exact hAX.eq_of_eventuallyEq hAY heq

end Preiss
