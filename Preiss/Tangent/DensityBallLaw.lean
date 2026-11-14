import Preiss.Tangent.Defs
import Preiss.Tangent.BlowupSupport
import FormalizingGMT.TangentMeasures.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # The centered ball law of dimensionally normalized tangents -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem dimensionalBlowup_ball_mass_tendsto
    (μ : Measure (Euclidean n)) (x : Euclidean n) {q : ℝ} (hq : 0 ≤ q)
    (hd : Tendsto (fun t : ℝ => μ (closedBall x t) / ENNReal.ofReal (t ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal q)))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun i => dimensionalBlowup m μ x (r i) (closedBall 0 R)) atTop
      (𝓝 (ENNReal.ofReal (q * R ^ m))) := by
  have hrR : Tendsto (fun i => r i * R) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using hr0.mul_const R
    · exact Eventually.of_forall fun i => mul_pos (hr i) hR
  have ht := ENNReal.Tendsto.mul_const (hd.comp hrR)
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (R ^ m) ≠ ∞))
  rw [← ENNReal.ofReal_mul hq] at ht
  apply ht.congr'
  exact Eventually.of_forall fun i => by
    change (μ (closedBall x (r i * R)) / ENNReal.ofReal ((r i * R) ^ m)) *
      ENNReal.ofReal (R ^ m) = dimensionalBlowup m μ x (r i) (closedBall 0 R)
    rw [dimensionalBlowup, Measure.smul_apply, smul_eq_mul,
      show (fun z : Euclidean n => (r i)⁻¹ • (z - x)) = blowUpMap x (r i) from rfl,
      map_blowUp_apply_closedBall μ x (hr i), mul_pow,
      ENNReal.ofReal_mul (pow_nonneg (hr i).le m), div_eq_mul_inv,
      ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
    calc
      μ (closedBall x (r i * R)) *
          ((ENNReal.ofReal (r i ^ m))⁻¹ * (ENNReal.ofReal (R ^ m))⁻¹) *
          ENNReal.ofReal (R ^ m) =
        (ENNReal.ofReal (r i ^ m))⁻¹ * μ (closedBall x (r i * R)) *
          ((ENNReal.ofReal (R ^ m))⁻¹ * ENNReal.ofReal (R ^ m)) := by ac_rfl
      _ = _ := by
        rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (pow_pos hR m)).ne'
          ENNReal.ofReal_ne_top, mul_one]

theorem dimensionalTangent_ball_law_at_zero
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    {q : ℝ} (hq : 0 < q)
    (hd : Tendsto (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal q)))
    (ν : Measure (Euclidean n)) (hν : IsDimensionalTangent m μ ν x) :
    (∀ R : ℝ, 0 < R → ν (closedBall 0 R) = ENNReal.ofReal (q * R ^ m)) ∧
      (0 : Euclidean n) ∈ ν.support := by
  obtain ⟨r, hr, hr0, hlim⟩ := hν.2.2
  let τ (i : ℕ) := dimensionalBlowup m μ x (r i)
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds τ ν
    (fun i => regular_dimensionalBlowup μ inferInstance x (hr i)) hν.1).mp hlim
  have hmass (R : ℝ) (hR : 0 < R) : Tendsto (fun i => τ i (closedBall 0 R)) atTop
      (𝓝 (ENNReal.ofReal (q * R ^ m))) :=
    dimensionalBlowup_ball_mass_tendsto μ x hq.le hd r hr hr0 R hR
  have hball (R : ℝ) (hR : 0 < R) : ν (closedBall 0 R) = ENNReal.ofReal (q * R ^ m) := by
    apply le_antisymm
    · have key (S : ℝ) (hRS : R < S) : ν (closedBall 0 R) ≤ ENNReal.ofReal (q * S ^ m) := by
        calc
          ν (closedBall 0 R) ≤ ν (ball 0 S) := measure_mono (closedBall_subset_ball hRS)
          _ ≤ liminf (fun i => τ i (ball 0 S)) atTop := hb.2 _ isOpen_ball
          _ ≤ liminf (fun i => τ i (closedBall 0 S)) atTop :=
            liminf_le_liminf (Eventually.of_forall fun _ => measure_mono ball_subset_closedBall)
          _ = _ := (hmass S (hR.trans hRS)).liminf_eq
      have hcont : Tendsto (fun S : ℝ => ENNReal.ofReal (q * S ^ m)) (𝓝[>] R)
          (𝓝 (ENNReal.ofReal (q * R ^ m))) :=
        ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow m))).tendsto R).mono_left
          nhdsWithin_le_nhds
      exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)
    · calc
        ENNReal.ofReal (q * R ^ m) = limsup (fun i => τ i (closedBall 0 R)) atTop :=
          (hmass R hR).limsup_eq.symm
        _ ≤ ν (closedBall 0 R) := hb.1 _ (isCompact_closedBall _ _)
  refine ⟨hball, ?_⟩
  apply Metric.nhds_basis_ball.mem_measureSupport.mpr
  intro R hR
  have hpos : 0 < ν (closedBall 0 (R / 2)) := by
    rw [hball (R / 2) (half_pos hR)]
    exact ENNReal.ofReal_pos.mpr (mul_pos hq (pow_pos (half_pos hR) m))
  exact hpos.trans_le (measure_mono (closedBall_subset_ball (half_lt_self hR)))

end Preiss
