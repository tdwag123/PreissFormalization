module

public import Preiss.Analysis.CoveringImage
public import Preiss.Rectifiability.ProjectionEstimate
public import Mathlib.Tactic

/-! # Quantitative projection bounds from uniform tubes and cone escape -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}


set_option maxHeartbeats 1500000 in
theorem measure_projection_le_of_uniform_tubes_and_cone_escape (m n : ℕ) (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : Measure (Euclidean n)) (C D : Set (Euclidean n))
      (V : Plane m n) (δ R₀ R₁ ε : ℝ), D ⊆ C → 0 < δ → 0 < R₀ → 0 < R₁ →
      0 < ε → ε ≤ 1 →
      (∀ a ∈ D, ∀ r : ℝ, 0 < r → r < R₀ →
        ENNReal.ofReal (δ * r ^ m) ≤ μ (ball a r)) →
      (∀ a ∈ D, ∀ s : ℝ, 0 < s → s < R₁ → ∃ W : Plane m n,
        C ∩ ball a (2 * s) ⊆ closedTube a W ((ε / 100) * s)) →
      (∀ a ∈ D, ∀ r : ℝ, 0 < r → ∃ b ∈ C ∩ ball a r, b ∉ cone a V (1 / ε)) →
      (Measure.hausdorffMeasure (m : ℝ)) (proj V '' D) ≤
        ENNReal.ofReal ((K / δ) * ε) * μ univ := by
  obtain ⟨L, hL, hslab⟩ := hausdorffMeasure_projected_tube_le m n hm
  refine ⟨4 * L * 5 ^ m, by positivity, ?_⟩
  intro μ C D V δ R₀ R₁ ε hDC hδ hR₀ hR₁ hε hε1 hlower htube hescape
  apply measure_image_le_mul_of_ball_image_bounds μ (Measure.hausdorffMeasure (m : ℝ))
    (proj V) D (ENNReal.ofReal (((4 * L * 5 ^ m) / δ) * ε)) 1
  intro a ha
  let t := min 1 (min (R₀ / 2) (R₁ / 20))
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨b, hb, hbout⟩ := hescape a ha t ht
  obtain ⟨hba, hP⟩ := norm_projection_lt_of_outside_cone V a b hε hbout
  let r := ‖b - a‖
  have hr : 0 < r := norm_pos_iff.mpr hba
  have hrt : r < t := by simpa only [mem_ball, dist_eq_norm] using hb.2
  have hr1 : r ≤ 1 := hrt.le.trans (min_le_left _ _)
  have hrR₀ : r < R₀ := by
    have hh : t ≤ R₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hrR₁ : 10 * r < R₁ := by
    have hh : t ≤ R₁ / 20 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨W, hW⟩ := htube a ha (10 * r) (by positivity) hrR₁
  have hnear : infDist (b - a) (W.1 : Set (Euclidean n)) ≤ (ε / 10) * ‖b - a‖ := by
    have hb' : b ∈ C ∩ ball a (2 * (10 * r)) := by
      refine ⟨hb.1, ?_⟩
      change ‖b - a‖ < 2 * (10 * r)
      dsimp only [r] at hr ⊢
      linarith
    have hh := hW hb'
    change infDist (b - a) (W.1 : Set (Euclidean n)) ≤ (ε / 100) * (10 * r) at hh
    convert hh using 1 <;> dsimp [r] <;> ring
  obtain ⟨w, hw, hnorm, hprojw⟩ := exists_unit_small_projection_of_near_plane V W (b - a)
    hba hε.le (show 0 ≤ ε / 10 by positivity) (by linarith) hnear hP.le
  have hprojw' : ‖proj V w‖ ≤ 3 * ε := hprojw.trans (by linarith)
  have hsub : proj V '' (D ∩ ball a (5 * r)) ⊆
      proj V '' (closedTube a W ((ε / 50) * (5 * r)) ∩ closedBall a (5 * r)) := by
    apply image_mono
    intro x hx
    refine ⟨?_, ball_subset_closedBall hx.2⟩
    have hh := hW ⟨hDC hx.1, ball_subset_ball (show 5 * r ≤ 2 * (10 * r) by linarith) hx.2⟩
    convert hh using 1 <;> ring
  have himage := (measure_mono hsub).trans (hslab V W a w (5 * r) (ε / 50) (3 * ε)
    (by positivity) (by positivity) (by positivity) hw hnorm hprojw')
  have hcoeff : L * (3 * ε + ε / 50) * 5 ^ m ≤ (4 * L * 5 ^ m) * ε := by
    have hh := mul_le_mul_of_nonneg_left (show 3 * ε + ε / 50 ≤ 4 * ε by linarith) hL.le
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ (5 : ℝ) ^ m by positivity)
    nlinarith
  have himage' : (Measure.hausdorffMeasure (m : ℝ)) (proj V '' (D ∩ ball a (5 * r))) ≤
      ENNReal.ofReal ((4 * L * 5 ^ m) * ε * r ^ m) := by
    apply himage.trans
    apply ENNReal.ofReal_le_ofReal
    rw [mul_pow]
    have hh := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr.le m)
    simpa only [mul_assoc] using hh
  refine ⟨r, hr, hr1, himage'.trans ?_⟩
  have heq : ENNReal.ofReal ((4 * L * 5 ^ m) * ε * r ^ m) =
      ENNReal.ofReal (((4 * L * 5 ^ m) / δ) * ε) * ENNReal.ofReal (δ * r ^ m) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [hδ.ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hlower a ha r hr hrR₀) bot_le

end Preiss
