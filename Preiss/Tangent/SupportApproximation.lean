import Preiss.Tangent.Defs
import Preiss.Tangent.BlowupSupport
import Preiss.Geometry.RescaledDistance
import FormalizingGMT.TangentMeasures.Basic
import Mathlib.Tactic.Linarith
import Preiss.Density.Defs
import Preiss.Analysis.MeasureHull
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.HausdorffDistance

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal
namespace Preiss
variable {n m : ℕ}

/-- Relative measure-density one, expressed without division by a possibly zero ball mass. -/
def IsMeasureDensityOnePoint (μ : Measure (Euclidean n)) (H : Set (Euclidean n))
    (a : Euclidean n) : Prop :=
  ∀ γ : ℝ≥0∞, 0 < γ → ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
    μ (closedBall a ρ \ H) ≤ γ * μ (closedBall a ρ)

/-- Density one and vague convergence alone force the rescaled set to approach the limit support. -/
theorem dist_set_rescaled_tendsto_zero_of_densityOne
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (D : Set (Euclidean n)) (hD : μ D ≠ ∞) (a : Euclidean n)
    (hdens : IsMeasureDensityOnePoint μ (toMeasurable μ D) a)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    (hlim : Measure.WeaklyConverges (fun i => dimensionalBlowup m μ a (r i)) ν)
    (y : Euclidean n) (hy : y ∈ ν.support) :
    Tendsto (fun i => infDist (a + r i • y) D / r i) atTop (𝓝 0) := by
  classical
  letI : ν.Regular := hν
  let τ (i : ℕ) := dimensionalBlowup m μ a (r i)
  let c (i : ℕ) : ℝ≥0∞ := (ENNReal.ofReal ((r i) ^ m))⁻¹
  have hτreg (i : ℕ) : (τ i).Regular := regular_dimensionalBlowup μ hμ a (hr i)
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds τ ν hτreg hν).mp hlim
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hpos : 0 < ν (ball y ε) :=
    (Measure.mem_support_iff_forall y).mp hy _ (ball_mem_nhds y hε)
  obtain ⟨δ, hδ, hδν⟩ := exists_between hpos
  have hlow : ∀ᶠ i in atTop, δ < τ i (ball y ε) :=
    eventually_lt_of_lt_liminf (hδν.trans_le (hb.2 _ isOpen_ball))
  let S := ‖y‖ + ε + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hballsub : ball y ε ⊆ closedBall (0 : Euclidean n) S := by
    intro z hz
    have hz' : dist z y < ε := hz
    have htri := dist_triangle z y 0
    change dist z 0 ≤ S
    dsimp [S]
    simp only [dist_zero_right] at htri ⊢
    linarith
  let M : ℝ≥0∞ := ν (closedBall 0 S) + 1
  have hMtop : M ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨(isCompact_closedBall (0 : Euclidean n) S).measure_lt_top.ne, ENNReal.one_ne_top⟩
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hmass : ∀ᶠ i in atTop, τ i (closedBall 0 S) ≤ M := by
    apply (eventually_lt_of_limsup_lt ?_).mono fun _ hi => hi.le
    exact (hb.1 _ (isCompact_closedBall _ _)).trans_lt
      (ENNReal.lt_add_right (isCompact_closedBall (0 : Euclidean n) S).measure_lt_top.ne one_ne_zero)
  have hrad : Tendsto (fun i => r i * S) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using hr0.mul_const S
    · exact Eventually.of_forall fun i => mul_pos (hr i) hS
  have hdensevent := hrad.eventually (hdens (δ / M) (ENNReal.div_pos hδ.ne' hMtop))
  filter_upwards [hlow, hmass, hdensevent] with i hi hmass hiD
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg infDist_nonneg (hr i).le)]
  by_contra hnot
  have hfar : ε * r i ≤ infDist (a + r i • y) D :=
    (le_div_iff₀ (hr i)).mp (not_lt.mp hnot)
  let U := blowUpMap a (r i) ⁻¹' ball y ε
  have hU : MeasurableSet U := (measurable_blowUpMap a (r i)) measurableSet_ball
  have hdisj : Disjoint D U := by
    apply Set.disjoint_left.mpr
    intro z hzD hzU
    have hz : dist y (blowUpMap a (r i) z) < ε := by
      simpa only [U, mem_preimage, mem_ball, dist_comm] using hzU
    have hdist : dist (a + r i • y) z < ε * r i := by
      rw [dist_affine_rescale a y z (hr i)]
      exact (mul_lt_mul_of_pos_left hz (hr i)).trans_eq (mul_comm _ _)
    exact (not_lt_of_ge (hfar.trans (infDist_le_dist_of_mem hzD))) hdist
  have hnull := measure_toMeasurable_inter_eq_zero_of_disjoint μ D U hD hU hdisj
  have hhole : μ U = μ (U \ toMeasurable μ D) := by
    rw [← measure_inter_add_sdiff U (measurableSet_toMeasurable μ D), inter_comm,
      hnull, zero_add]
  have hsub : U ⊆ closedBall a (r i * S) := by
    rw [← blowUpMap_preimage_closedBall a (hr i) S]
    exact preimage_mono hballsub
  have hsmall : τ i (ball y ε) ≤ δ := by
    calc
      τ i (ball y ε) = c i * μ U := by
        change (c i • μ.map (blowUpMap a (r i))) (ball y ε) = _
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply
          (measurable_blowUpMap a (r i)) measurableSet_ball]
      _ = c i * μ (U \ toMeasurable μ D) := by rw [hhole]
      _ ≤ c i * μ (closedBall a (r i * S) \ toMeasurable μ D) :=
        mul_le_mul' le_rfl (measure_mono (sdiff_subset_sdiff_left hsub))
      _ ≤ c i * ((δ / M) * μ (closedBall a (r i * S))) := mul_le_mul' le_rfl hiD
      _ = (δ / M) * τ i (closedBall 0 S) := by
        change _ = (δ / M) * (c i • μ.map (blowUpMap a (r i))) (closedBall 0 S)
        rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_closedBall μ a (hr i)]
        ac_rfl
      _ ≤ (δ / M) * M := mul_le_mul' le_rfl hmass
      _ = δ := ENNReal.div_mul_cancel hMpos.ne' hMtop
  exact (not_lt_of_ge hsmall) hi


/-- The set need not be measurable; density one is imposed on its measurable hull. -/
theorem dist_badSet_rescaled_tendsto_zero
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (D : Set (Euclidean n)) (hD : μ D ≠ ∞) (a : Euclidean n) (ha : a ∈ D)
    (hdens : IsMeasureDensityOnePoint μ (toMeasurable μ D) a)
    (hupper : dimensional_upper_density μ.toOuterMeasure (m : ℝ) a < ∞)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    (hlim : Measure.WeaklyConverges (fun i => dimensionalBlowup m μ a (r i)) ν)
    (y : Euclidean n) (hy : y ∈ ν.support) :
    Tendsto (fun i => infDist (a + r i • y) D / r i) atTop (𝓝 0) := by
  exact dist_set_rescaled_tendsto_zero_of_densityOne μ ν hμ hν D hD a hdens r hr hr0 hlim y hy

/-- Approximate nearest points suffice; the arbitrary set `D` need not be closed. -/
theorem exists_badSet_points_rescaled_tendsto
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (D : Set (Euclidean n)) (hD : μ D ≠ ∞) (a : Euclidean n) (ha : a ∈ D)
    (hdens : IsMeasureDensityOnePoint μ (toMeasurable μ D) a)
    (hupper : dimensional_upper_density μ.toOuterMeasure (m : ℝ) a < ∞)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    (hlim : Measure.WeaklyConverges (fun i => dimensionalBlowup m μ a (r i)) ν)
    (y : Euclidean n) (hy : y ∈ ν.support) :
    ∃ a' : ℕ → Euclidean n, (∀ i, a' i ∈ D) ∧
      Tendsto (fun i => (r i)⁻¹ • (a' i - a)) atTop (𝓝 y) := by
  exact exists_points_rescaled_tendsto_of_infDist D ⟨a, ha⟩ a y r hr
    (dist_set_rescaled_tendsto_zero_of_densityOne μ ν hμ hν D hD a hdens r hr hr0 hlim y hy)

end Preiss
