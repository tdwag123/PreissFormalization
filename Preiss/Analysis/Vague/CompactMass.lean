import FormalizingGMT.WeakConvergence.Basic
import Preiss.Geometry.Euclidean

/-! # Compact-set and uniform ball-mass consequences of vague convergence -/
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {n : ℕ}

theorem tendsto_mass_compact_null_of_vague
    (ν : ℕ → Measure (Euclidean n)) (μ : Measure (Euclidean n))
    (hν : ∀ i, (ν i).Regular) (hμ : μ.Regular)
    (hlim : Measure.WeaklyConverges ν μ) {K : Set (Euclidean n)}
    (hK : IsCompact K) (hzero : μ K = 0) :
    Tendsto (fun i => ν i K) atTop (𝓝 0) := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds ν μ hν hμ).mp hlim
  apply tendsto_of_le_liminf_of_limsup_le
    (show (0 : ℝ≥0∞) ≤ atTop.liminf (fun i => ν i K) from zero_le)
  simpa only [hzero] using hb.1 K hK

theorem eventually_uniform_ball_mass_lower_bound_of_vague
    (ν : ℕ → Measure (Euclidean n)) (μ : Measure (Euclidean n))
    (hν : ∀ i, (ν i).Regular) (hμ : μ.Regular)
    (hlim : Measure.WeaklyConverges ν μ) {K : Set (Euclidean n)}
    (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    (hpos : ∀ z ∈ K, 0 < μ (ball z (η / 2))) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ i in atTop, ∀ z ∈ K,
      ENNReal.ofReal a ≤ ν i (ball z η) := by
  classical
  letI : μ.Regular := hμ
  by_cases hne : K.Nonempty
  swap
  · refine ⟨1, zero_lt_one, Filter.Eventually.of_forall ?_⟩
    intro i z hz
    exact False.elim (hne ⟨z, hz⟩)
  let a (z : K) : ℝ := (μ (ball z.val (η / 2))).toReal / 2
  have ha (z : K) : 0 < a z :=
    div_pos (ENNReal.toReal_pos (hpos z z.property).ne' measure_ball_ne_top) (by norm_num)
  have halt (z : K) : ENNReal.ofReal (a z) < μ (ball z.val (η / 2)) := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (ha z).le measure_ball_ne_top).mpr
    dsimp [a]
    have hp := ENNReal.toReal_pos (hpos z z.property).ne' measure_ball_ne_top
    linarith
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds ν μ hν hμ).mp hlim
  have hev (z : K) : ∀ᶠ i in atTop,
      ENNReal.ofReal (a z) < ν i (ball z.val (η / 2)) :=
    eventually_lt_of_lt_liminf ((halt z).trans_le (hb.2 _ isOpen_ball))
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun z : K => ball z.val (η / 2)) (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (by linarith)⟩)
  have hsne : s.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hw, _⟩ := mem_iUnion₂.mp (hs hz)
    exact ⟨w, hw⟩
  refine ⟨s.inf' hsne a, (Finset.lt_inf'_iff _).mpr (fun z _ => ha z), ?_⟩
  have hall : ∀ᶠ i in atTop, ∀ z ∈ s,
      ENNReal.ofReal (a z) < ν i (ball z.val (η / 2)) :=
    (Filter.eventually_all_finset s).mpr (fun z _ => hev z)
  filter_upwards [hall] with i hi z hz
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
  have hsub : ball w.val (η / 2) ⊆ ball z η := by
    intro y hy
    have h1 := mem_ball.mp hy
    have h2 := mem_ball.mp hzw
    have htriangle := dist_triangle y w.val z
    rw [dist_comm w.val z] at htriangle
    exact mem_ball.mpr (by linarith)
  exact (ENNReal.ofReal_le_ofReal (Finset.inf'_le _ hw)).trans
    ((hi w hw).le.trans (measure_mono hsub))

end Preiss
