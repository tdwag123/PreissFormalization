module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Boundary nullity from a continuous centered ball profile

A finite closed-ball mass profile continuous at a positive radius has no boundary atom.
The resulting a.e. equality identifies open- and closed-ball integrals without extra
integrability assumptions, using the usual total Bochner integral convention.
-/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss

section General
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A continuous, finite centered closed-ball profile has no positive-radius jump. -/
theorem ball_ae_eq_closedBall_of_continuous_profile
    (μ : Measure X) (x : X) (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hf : ContinuousAt f r)
    (hball : ∀ s : ℝ, 0 < s → μ (closedBall x s) = ENNReal.ofReal (f s)) :
    ball x r =ᵐ[μ] closedBall x r := by
  have hlower : ENNReal.ofReal (f r) ≤ μ (ball x r) := by
    have hcont : Tendsto (fun s : ℝ => ENNReal.ofReal (f s)) (𝓝[<] r)
        (𝓝 (ENNReal.ofReal (f r))) :=
      (ENNReal.continuous_ofReal.continuousAt.comp hf).tendsto.mono_left
        nhdsWithin_le_nhds
    refine le_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds hr)] with s hsr hs
    rw [← hball s hs]
    exact measure_mono (closedBall_subset_ball hsr)
  apply ae_eq_of_subset_of_measure_ge ball_subset_closedBall
  · simpa only [hball r hr] using hlower
  · exact measurableSet_ball.nullMeasurableSet
  · rw [hball r hr]
    exact ENNReal.ofReal_ne_top

theorem measure_sphere_eq_zero_of_continuous_profile
    (μ : Measure X) (x : X) (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hf : ContinuousAt f r)
    (hball : ∀ s : ℝ, 0 < s → μ (closedBall x s) = ENNReal.ofReal (f s)) :
    μ (sphere x r) = 0 := by
  have hae := ball_ae_eq_closedBall_of_continuous_profile μ x f hr hf hball
  have hfin : μ (ball x r) ≠ ∞ := by
    rw [measure_congr hae, hball r hr]
    exact ENNReal.ofReal_ne_top
  rw [← closedBall_sdiff_ball,
    measure_sdiff ball_subset_closedBall measurableSet_ball.nullMeasurableSet hfin,
    measure_congr hae, tsub_self]

theorem integral_ball_eq_closedBall_of_continuous_profile
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) (x : X) (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hf : ContinuousAt f r)
    (hball : ∀ s : ℝ, 0 < s → μ (closedBall x s) = ENNReal.ofReal (f s))
    (g : X → F) :
    (∫ z in ball x r, g z ∂μ) = ∫ z in closedBall x r, g z ∂μ :=
  setIntegral_congr_set (ball_ae_eq_closedBall_of_continuous_profile μ x f hr hf hball)

end General

end Preiss
