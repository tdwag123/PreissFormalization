import Preiss.Geometry.Euclidean
import FormalizingGMT.WeakConvergence.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace Preiss
variable {n : ℕ}

theorem exists_support_sequence_of_vague
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) (x : Euclidean n) (hx : x ∈ ν.support) :
    ∃ y : ℕ → Euclidean n, (∀ᶠ i in atTop, y i ∈ (μ i).support) ∧
      Tendsto y atTop (𝓝 x) := by
  classical
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds μ ν hμ hν).mp hlim
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      ∃ z ∈ (μ i).support, dist z x < ε := by
    intro ε hε
    have hpos : 0 < ν (ball x ε) :=
      (Measure.mem_support_iff_forall x).mp hx _ (ball_mem_nhds x hε)
    have hevent : ∀ᶠ i in atTop, 0 < μ i (ball x ε) :=
      eventually_lt_of_lt_liminf (hpos.trans_le (hb.2 _ isOpen_ball))
    filter_upwards [hevent] with i hi
    obtain ⟨z, hzball, hzsupp⟩ := Measure.nonempty_inter_support_of_pos hi
    exact ⟨z, hzsupp, hzball⟩
  have hchoice (i : ℕ) : ∃ y : Euclidean n, (μ i).support.Nonempty →
      y ∈ (μ i).support ∧ infDist x (μ i).support = dist x y := by
    by_cases hne : (μ i).support.Nonempty
    · obtain ⟨y, hy, hdist⟩ :=
        (Measure.isClosed_support (μ := μ i)).exists_infDist_eq_dist hne x
      exact ⟨y, fun _ => ⟨hy, hdist⟩⟩
    · exact ⟨x, fun h => (hne h).elim⟩
  choose y hy using hchoice
  refine ⟨y, ?_, ?_⟩
  · filter_upwards [hnear 1 zero_lt_one] with i hi
    obtain ⟨z, hz, _⟩ := hi
    exact (hy i ⟨z, hz⟩).1
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hnear ε hε] with i hi
    obtain ⟨z, hz, hzx⟩ := hi
    have hchosen := hy i ⟨z, hz⟩
    calc dist (y i) x = infDist x (μ i).support := by rw [dist_comm, ← hchosen.2]
      _ ≤ dist x z := infDist_le_dist_of_mem hz
      _ < ε := by rwa [dist_comm]

theorem mem_support_of_vague_lower_ball_bound
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) (x : ℕ → Euclidean n) (y : Euclidean n)
    (hxy : Tendsto x atTop (𝓝 y)) (hx : ∀ i, x i ∈ (μ i).support)
    (hlower : ∀ r > 0, ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ᶠ i in atTop, c ≤ μ i (ball (x i) r)) : y ∈ ν.support := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds μ ν hμ hν).mp hlim
  apply Metric.nhds_basis_ball.mem_measureSupport.mpr
  intro r hr
  obtain ⟨c, hc, hcevent⟩ := hlower (r / 2) (half_pos hr)
  have hxevent : ∀ᶠ i in atTop, dist (x i) y < r / 4 :=
    Metric.tendsto_nhds.mp hxy (r / 4) (by linarith)
  have hevent : ∀ᶠ i in atTop, c ≤ μ i (closedBall y (3 * r / 4)) := by
    filter_upwards [hcevent, hxevent] with i hi hdist
    apply hi.trans (measure_mono ?_)
    intro z hz
    have hz' : dist z (x i) < r / 2 := hz
    have htri := dist_triangle z (x i) y
    change dist z y ≤ 3 * r / 4
    linarith
  have hbound : c ≤ ν (closedBall y (3 * r / 4)) := by
    calc c = liminf (fun _ : ℕ => c) atTop := (liminf_const _).symm
      _ ≤ liminf (fun i => μ i (closedBall y (3 * r / 4))) atTop :=
        liminf_le_liminf hevent
      _ ≤ limsup (fun i => μ i (closedBall y (3 * r / 4))) atTop := liminf_le_limsup
      _ ≤ ν (closedBall y (3 * r / 4)) := hb.1 _ (isCompact_closedBall _ _)
  exact hc.trans_le (hbound.trans
    (measure_mono (closedBall_subset_ball (by linarith : 3 * r / 4 < r))))

end Preiss
