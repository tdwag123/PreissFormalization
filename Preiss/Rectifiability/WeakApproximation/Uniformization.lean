module

public import Preiss.Rectifiability.WeakApproximation.Basic
public import Preiss.Geometry.PlaneTopology
public import Preiss.Geometry.Cones
public import Preiss.Analysis.MovingSets
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def weakApproximationGoodSet (m : ℕ) (μ : Measure (Euclidean n)) (η a R : ℝ) :
    Set (Euclidean n) :=
  {x | ∀ r : ℝ, 0 < r → r < R → ∃ V : Plane m n,
    μ (ball x r \ closedTube x V (η * r)) ≤ ENNReal.ofReal (η * r ^ m) ∧
    ∀ z : Euclidean n, z - x ∈ V.1 → z ∈ ball x r →
      ENNReal.ofReal (a * r ^ m) ≤ μ (closedBall z (η * r))}

theorem isClosed_weakApproximationGoodSet (μ : Measure (Euclidean n))
    [IsFiniteMeasure μ] [μ.Regular] {η a R : ℝ}
    (hη : 0 < η) (ha : 0 < a) (hR : 0 < R) :
    IsClosed (weakApproximationGoodSet m μ η a R) := by
  apply IsSeqClosed.isClosed
  intro x y hx hxy r hr hrR
  choose V hupper hlower using fun i ↦ hx i r hr hrR
  obtain ⟨W, φ, hφ, hVW⟩ := exists_tendsto_planeProjection_subseq V
  have hxy' : Tendsto (fun i ↦ x (φ i)) atTop (𝓝 y) := hxy.comp hφ.tendsto_atTop
  have heval : Continuous (fun p : (Euclidean n →L[ℝ] Euclidean n) × Euclidean n ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  refine ⟨W, ?_, ?_⟩
  · apply measure_le_of_pointwise_eventually_mem μ
      (fun i ↦ ball (x (φ i)) r \ closedTube (x (φ i)) (V (φ i)) (η * r))
    · exact Eventually.of_forall fun i ↦ hupper (φ i)
    · rintro z ⟨hzball, hztube⟩
      have hzdist : Tendsto (fun i ↦ dist z (x (φ i))) atTop (𝓝 (dist z y)) :=
        tendsto_const_nhds.dist hxy'
      have hsub : Tendsto (fun i ↦ z - x (φ i)) atTop (𝓝 (z - y)) :=
        tendsto_const_nhds.sub hxy'
      have hproj := heval.tendsto (planeProjection W, z - y) |>.comp (hVW.prodMk_nhds hsub)
      have hnorm : Tendsto
          (fun i ↦ ‖(z - x (φ i)) - planeProjection (V (φ i)) (z - x (φ i))‖)
          atTop (𝓝 ‖(z - y) - planeProjection W (z - y)‖) :=
        (hsub.sub hproj).norm
      have hzt : η * r < ‖(z - y) - planeProjection W (z - y)‖ := by
        have hgt : η * r < infDist (z - y) (W.1 : Set (Euclidean n)) := lt_of_not_ge hztube
        simpa only [infDist_submodule_eq_norm_sub_starProjection, planeProjection] using hgt
      filter_upwards [hzdist.eventually_lt_const hzball, hnorm.eventually_const_lt hzt] with i hi1 hi2
      refine ⟨hi1, ?_⟩
      change ¬ infDist (z - x (φ i)) ((V (φ i)).1 : Set (Euclidean n)) ≤ η * r
      rw [infDist_submodule_eq_norm_sub_starProjection]
      exact not_le_of_gt hi2
  · intro z hz hzr
    let z' : ℕ → Euclidean n := fun i ↦ x (φ i) + planeProjection (V (φ i)) (z - y)
    have hfix : planeProjection W (z - y) = z - y :=
      W.1.starProjection_eq_self_iff.mpr hz
    have hproj := heval.tendsto (planeProjection W, z - y) |>.comp
      (hVW.prodMk_nhds (tendsto_const_nhds (x := z - y)))
    have hzz : Tendsto z' atTop (𝓝 z) := by
      have heq : y + planeProjection W (z - y) = z := by rw [hfix]; abel
      simpa only [z', Function.comp_def, heq] using hxy'.add hproj
    have hzd : Tendsto (fun i ↦ dist (z' i) (x (φ i))) atTop (𝓝 (dist z y)) :=
      hzz.dist hxy'
    apply le_measure_of_pointwise_eventually_notMem μ (fun i ↦ closedBall (z' i) (η * r))
    · exact fun i ↦ isClosed_closedBall.measurableSet.nullMeasurableSet
    · filter_upwards [hzd.eventually_lt_const hzr] with i hi
      apply hlower (φ i) (z' i) _ hi
      have heq : z' i - x (φ i) = planeProjection (V (φ i)) (z - y) := by dsimp [z']; abel
      rw [heq]
      exact Submodule.coe_mem ((V (φ i)).1.orthogonalProjectionOnto (z - y))
    · intro w hw
      have hgt : η * r < dist w z := lt_of_not_ge hw
      exact ((tendsto_const_nhds.dist hzz).eventually_const_lt hgt).mono fun i hi ↦
        not_le_of_gt hi

theorem weaklyLinearlyApproximableAt_iff_goodSet_exhaustion
    (μ : Measure (Euclidean n)) (x : Euclidean n) :
    MeasureWeaklyLinearlyApproximableAt m μ x ↔
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, x ∈
        weakApproximationGoodSet m μ η (1 / (N + 1 : ℝ)) (1 / (N + 1 : ℝ)) := by
  constructor
  · intro h η hη
    obtain ⟨a, ha, R, hR, happ⟩ := h η hη
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min ha hR)
    refine ⟨N, ?_⟩
    intro r hr hrN
    obtain ⟨V, hupper, hlower⟩ := happ r hr (hrN.trans (hN.trans_le (min_le_right _ _)))
    refine ⟨V, hupper.le, ?_⟩
    intro z hz hzr
    have hcoef : 1 / (N + 1 : ℝ) ≤ a := (hN.trans_le (min_le_left _ _)).le
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr.le m))).trans
      ((hlower z hz hzr).trans (measure_mono ball_subset_closedBall))
  · intro h η hη
    obtain ⟨N, hN⟩ := h (η / 2) (half_pos hη)
    refine ⟨1 / (N + 1 : ℝ), by positivity, 1 / (N + 1 : ℝ), by positivity, ?_⟩
    intro r hr hrN
    obtain ⟨V, hupper, hlower⟩ := hN r hr hrN
    refine ⟨V, ?_, ?_⟩
    · have hsub : ball x r \ closedTube x V (η * r) ⊆
          ball x r \ closedTube x V ((η / 2) * r) := by
        rintro z ⟨hz, hzt⟩
        refine ⟨hz, ?_⟩
        intro hsmall
        exact hzt (hsmall.trans (mul_le_mul_of_nonneg_right (half_le_self hη.le) hr.le))
      apply lt_of_le_of_lt ((measure_mono hsub).trans hupper)
      exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hη (pow_pos hr m))).mpr
        (mul_lt_mul_of_pos_right (half_lt_self hη) (pow_pos hr m))
    · intro z hz hzr
      exact (hlower z hz hzr).trans (measure_mono (closedBall_subset_ball
        (mul_lt_mul_of_pos_right (half_lt_self hη) hr)))

theorem exists_compact_uniform_weakApproximation_subset
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ] [μ.Regular]
    (E : Set (Euclidean n)) (hE : MeasurableSet E)
    (hw : ∀ᵐ x ∂μ.restrict E, MeasureWeaklyLinearlyApproximableAt m μ x)
    (A : Finset ℝ) (hA : ∀ η ∈ A, 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set (Euclidean n), IsCompact C ∧ C ⊆ E ∧
      μ (E \ C) < ENNReal.ofReal ε ∧ ∀ η ∈ A, ∃ N : ℕ,
        C ⊆ weakApproximationGoodSet m μ η (1 / (N + 1 : ℝ)) (1 / (N + 1 : ℝ)) := by sorry

theorem subset_tube_of_lower_mass_and_small_outside_mass
    (μ : Measure (Euclidean n)) (C : Set (Euclidean n)) (a : Euclidean n)
    (V : Plane m n) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hr : 0 < r)
    (hlower : ∀ z ∈ C, ENNReal.ofReal (δ * (η * r / 2) ^ m) ≤
      μ (ball z (η * r / 2)))
    (herror : μ (ball a (2 * r) \ closedTube a V (η * r / 2)) <
      ENNReal.ofReal (δ * (η * r / 2) ^ m)) :
    C ∩ ball a r ⊆ closedTube a V (η * r) := by
  intro z hz
  by_contra hzt
  have hzdist : η * r < infDist (z - a) (V.1 : Set (Euclidean n)) := lt_of_not_ge hzt
  have hsub : ball z (η * r / 2) ⊆ ball a (2 * r) \ closedTube a V (η * r / 2) := by
    intro w hw
    have hwz : dist w z < η * r / 2 := hw
    have hza : dist z a < r := hz.2
    have hηr : η * r ≤ r := mul_le_of_le_one_left hr.le hη1
    refine ⟨?_, ?_⟩
    · have ht := dist_triangle w z a
      change dist w a < 2 * r
      linarith
    · intro hwt
      have hwdist : infDist (w - a) (V.1 : Set (Euclidean n)) ≤ η * r / 2 := hwt
      have hi := infDist_le_infDist_add_dist (x := z - a) (y := w - a)
        (s := (V.1 : Set (Euclidean n)))
      have hd : dist (z - a) (w - a) = dist z w := by
        simp only [dist_eq_norm]
        congr 1
        abel
      rw [hd, dist_comm z w] at hi
      linarith
  exact (not_lt_of_ge (hlower z hz.1)) ((measure_mono hsub).trans_lt herror)

end Preiss
