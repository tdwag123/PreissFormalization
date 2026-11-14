import Preiss.Tangent.Basic
import Preiss.Tangent.SupportApproximation
import Preiss.Tangent.MetricApproximation
import Preiss.Tangent.MovingCenters
import Preiss.Analysis.Vague.SecondCountable
import FormalizingGMT.TangentMeasures.DensityIneqToTangentsLemmas2
import Mathlib.Tactic.Linarith

/-! # Simultaneous recentering of dimensional tangents -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- An arbitrary set of centers with uniformly separated recentered tangent witnesses is null.
The set is not assumed measurable. -/
theorem measure_eq_zero_of_recenter_separation (M : VagueMetrization n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (D : Set (Euclidean n)) (hDfinite : μ D ≠ ∞)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (q : RegularEuclideanMeasure n) :
    letI := M.metric
    (∀ a ∈ D, ∃ (ν : Measure (Euclidean n)) (y : Euclidean n)
        (η : RegularEuclideanMeasure n),
      IsDimensionalTangent m μ ν a ∧ y ∈ ν.support ∧
      η.val = dimensionalBlowup m ν y 1 ∧ dist η q < ρ ∧
      ∀ (t : ℝ) (ht : 0 < t), t < δ →
        4 * ρ ≤ dist (⟨dimensionalBlowup m μ a t,
          regular_dimensionalBlowup μ inferInstance a ht⟩ : RegularEuclideanMeasure n) η) →
      μ D = 0 := by
  classical
  letI := M.metric
  intro hbad
  by_contra hpos
  obtain ⟨N, hN0, hpoint⟩ := exists_null_of_not_density_point μ inferInstance
    (measurableSet_toMeasurable μ D)
  have hne : (D \ N).Nonempty := by
    by_contra hn
    apply hpos
    apply measure_mono_null ?_ hN0
    intro x hx
    by_contra hxN
    exact hn ⟨x, hx, hxN⟩
  obtain ⟨a, ha, haN⟩ := hne
  have hdens : IsMeasureDensityOnePoint μ (toMeasurable μ D) a :=
    hpoint a ⟨subset_toMeasurable μ D ha, haN⟩
  obtain ⟨ν, y, η, hν, hy, hηeq, hηq, hsep⟩ := hbad a ha
  obtain ⟨r, hr, hr0, hlim⟩ := hν.2.2
  have hdist := dist_set_rescaled_tendsto_zero_of_densityOne μ ν inferInstance hν.1
    D hDfinite a hdens r hr hr0 hlim y hy
  obtain ⟨a', ha', hcenters⟩ := exists_points_rescaled_tendsto_of_infDist D ⟨a, ha⟩ a y r hr hdist
  have hconv := vague_dimensionalBlowup_moving_center μ ν inferInstance hν.1 a r hr hlim a' y hcenters
  rw [← hηeq] at hconv
  let τ (i : ℕ) : RegularEuclideanMeasure n :=
    ⟨dimensionalBlowup m μ (a' i) (r i), regular_dimensionalBlowup μ inferInstance (a' i) (hr i)⟩
  have ht : Tendsto τ atTop (𝓝 η) := (M.tendsto_iff τ η).mpr hconv
  have hclose : ∀ᶠ i in atTop, dist (τ i) η < ρ := Metric.tendsto_nhds.mp ht ρ hρ
  obtain ⟨i, hi, hri⟩ := (hclose.and (hr0.eventually_lt_const hδ)).exists
  obtain ⟨νi, yi, ηi, hνi, hyi, hηieq, hηiq, hsepi⟩ := hbad (a' i) (ha' i)
  have hfar := hsepi (r i) (hr i) hri
  change 4 * ρ ≤ dist (τ i) ηi at hfar
  have hηiq' : dist q ηi < ρ := by rwa [dist_comm]
  have htri₁ := dist_triangle (τ i) η ηi
  have htri₂ := dist_triangle η q ηi
  linarith


/-- One exceptional null set works for every tangent, support point, and positive radius. -/
theorem ae_recenter_dimensionalTangent_of_locallyFinite (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] :
    ∀ᵐ a ∂μ, ∀ ν : Measure (Euclidean n), IsDimensionalTangent m μ ν a →
      ∀ y ∈ ν.support, ∀ r : ℝ, 0 < r →
        IsDimensionalTangent m μ (dimensionalBlowup m ν y r) a := by
  classical
  obtain ⟨M, hM⟩ := exists_secondCountable_vagueMetrization n
  letI := M.metric
  letI : SecondCountableTopology (RegularEuclideanMeasure n) := hM
  letI : Nonempty (RegularEuclideanMeasure n) := ⟨⟨0, inferInstance⟩⟩
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (RegularEuclideanMeasure n)
  let ρ (l : ℕ) : ℝ := 1 / ((l : ℝ) + 1)
  have hρ (l : ℕ) : 0 < ρ l := by dsimp [ρ]; positivity
  let D (l k j N : ℕ) : Set (Euclidean n) := {a | ‖a‖ ≤ (N : ℝ) ∧
    ∃ (ν : Measure (Euclidean n)) (y : Euclidean n) (η : RegularEuclideanMeasure n),
      IsDimensionalTangent m μ ν a ∧ y ∈ ν.support ∧
      η.val = dimensionalBlowup m ν y 1 ∧ dist η (q j) < ρ l ∧
      ∀ (t : ℝ) (ht : 0 < t), t < ρ k →
        4 * ρ l ≤ dist (⟨dimensionalBlowup m μ a t,
          regular_dimensionalBlowup μ inferInstance a ht⟩ : RegularEuclideanMeasure n) η}
  have hnull (l k j N : ℕ) : μ (D l k j N) = 0 := by
    have hsub : D l k j N ⊆ closedBall (0 : Euclidean n) (N : ℝ) := by
      intro a ha
      simpa only [mem_closedBall, dist_zero_right] using ha.1
    have hfin : μ (D l k j N) ≠ ∞ :=
      ((measure_mono hsub).trans_lt (isCompact_closedBall (0 : Euclidean n) (N : ℝ)).measure_lt_top).ne
    exact measure_eq_zero_of_recenter_separation M μ (D l k j N) hfin
      (ρ l) (ρ k) (hρ l) (hρ k) (q j) (fun a ha => ha.2)
  have hae : ∀ᵐ a ∂μ, ∀ l k j N : ℕ, a ∉ D l k j N := by
    simp only [ae_all_iff]
    intro l k j N
    apply ae_iff.mpr
    simpa only [not_not, setOf_mem_eq] using hnull l k j N
  filter_upwards [hae] with a ha
  intro ν hν y hy s hs
  have hbase : IsDimensionalTangent m μ (dimensionalBlowup m ν y 1) a := by
    let η : RegularEuclideanMeasure n :=
      ⟨dimensionalBlowup m ν y 1, regular_dimensionalBlowup ν hν.1 y zero_lt_one⟩
    by_contra hnot
    obtain ⟨ε, hε, δ, hδ, hsep⟩ := exists_metric_separation_of_not_dimensionalTangent
      M μ a η (dimensionalBlowup_one_ne_zero_of_mem_support ν y hy) hnot
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    obtain ⟨j, hj⟩ := hq.mem_nhds (ball_mem_nhds η (hρ l))
    have hηq : dist η (q j) < ρ l := by simpa only [mem_ball, dist_comm] using hj
    obtain ⟨N, hN⟩ := exists_nat_ge ‖a‖
    apply ha l k j N
    refine ⟨hN, ν, y, η, hν, hy, rfl, hηq, ?_⟩
    intro t ht htk
    have htk' : t < δ := htk.trans hk
    have hsmall : 4 * ρ l ≤ ε := by dsimp [ρ]; linarith
    exact hsmall.trans (hsep t ht htk')
  simpa only [dimensionalBlowup_comp _ _ _ _ _ zero_lt_one hs, smul_zero,
    add_zero, one_mul] using hbase.dilate hs

theorem ae_recenter_dimensionalTangent (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (hm : 0 < m) (hmn : m ≤ n)
    (hdens : ∀ᵐ a ∂μ, HasPositiveFiniteDensityAt m μ a) :
    ∀ᵐ a ∂μ, ∀ ν : Measure (Euclidean n), IsDimensionalTangent m μ ν a →
      ∀ y ∈ ν.support, ∀ r : ℝ, 0 < r →
        IsDimensionalTangent m μ (dimensionalBlowup m ν y r) a := by
  exact ae_recenter_dimensionalTangent_of_locallyFinite μ

end Preiss
