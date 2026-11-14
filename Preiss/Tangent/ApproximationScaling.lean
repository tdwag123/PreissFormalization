import Preiss.Tangent.Blowup
import Preiss.Geometry.PlaneDistance
import FormalizingGMT.TangentMeasures.DensityIneqToTangentsLemmas1

/-! # Transferring normalized blow-up estimates to the original measure -/
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem dimensionalBlowup_apply_lt_iff (μ : Measure (Euclidean n)) (x : Euclidean n)
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) {S : Set (Euclidean n)} (hS : MeasurableSet S) :
    dimensionalBlowup m μ x r S < ENNReal.ofReal a ↔
      μ ((fun y => r⁻¹ • (y - x)) ⁻¹' S) < ENNReal.ofReal (a * r ^ m) := by
  have hD : ENNReal.ofReal (r ^ m) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'
  rw [dimensionalBlowup, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) hS, ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hD) (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul ha]

theorem le_dimensionalBlowup_apply_iff (μ : Measure (Euclidean n)) (x : Euclidean n)
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) {S : Set (Euclidean n)} (hS : MeasurableSet S) :
    ENNReal.ofReal a ≤ dimensionalBlowup m μ x r S ↔
      ENNReal.ofReal (a * r ^ m) ≤ μ ((fun y => r⁻¹ • (y - x)) ⁻¹' S) := by
  have hD : ENNReal.ofReal (r ^ m) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'
  rw [dimensionalBlowup, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) hS, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl hD) (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul ha]


theorem weakApproximation_scale_of_normalized_bounds
    (μ : Measure (Euclidean n)) (x : Euclidean n) (V : Plane m n)
    {r η a : ℝ} (hr : 0 < r) (hη : 0 < η) (ha : 0 ≤ a)
    (hup : dimensionalBlowup m μ x r
      (closedBall 0 1 ∩ {z | η ≤ infDist z (V.1 : Set (Euclidean n))}) < ENNReal.ofReal η)
    (hlo : ∀ z : Euclidean n, z ∈ V.1 → z ∈ closedBall 0 1 →
      ENNReal.ofReal a ≤ dimensionalBlowup m μ x r (ball z η)) :
    μ (ball x r \ {z | infDist (z-x) (V.1 : Set (Euclidean n)) ≤ η*r}) <
      ENNReal.ofReal (η*r^m) ∧
    ∀ z : Euclidean n, z-x ∈ V.1 → z ∈ ball x r →
      ENNReal.ofReal (a*r^m) ≤ μ (ball z (η*r)) := by
  let K : Set (Euclidean n) := closedBall 0 1 ∩
    {z | η ≤ infDist z (V.1 : Set (Euclidean n))}
  have hK : MeasurableSet K := measurableSet_closedBall.inter
    (isClosed_le continuous_const (continuous_infDist_pt _)).measurableSet
  have hnorm (z : Euclidean n) : ‖r⁻¹ • (z-x)‖ = r⁻¹ * ‖z-x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  constructor
  · have hmass := (dimensionalBlowup_apply_lt_iff μ x hr hη.le hK).mp hup
    apply lt_of_le_of_lt (measure_mono ?_) hmass
    intro z hz
    have hzball : ‖z-x‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz.1
    have hzaway : η*r < infDist (z-x) (V.1 : Set (Euclidean n)) := lt_of_not_ge hz.2
    change r⁻¹ • (z-x) ∈ K
    constructor
    · rw [mem_closedBall, dist_zero_right, hnorm]
      exact (inv_mul_lt_iff₀ hr).mpr (by simpa using hzball) |>.le
    · rw [Set.mem_setOf_eq, infDist_smul_plane, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      exact (le_inv_mul_iff₀ hr).mpr (by nlinarith)
  · intro z hzV hzB
    let w : Euclidean n := r⁻¹ • (z-x)
    have hwV : w ∈ V.1 := V.1.smul_mem _ hzV
    have hwB : w ∈ closedBall 0 1 := by
      rw [mem_closedBall, dist_zero_right]
      change ‖r⁻¹ • (z-x)‖ ≤ 1
      rw [hnorm]
      exact (inv_mul_lt_iff₀ hr).mpr (by simpa only [one_mul, mul_one, mem_ball, dist_eq_norm] using hzB) |>.le
    have hmass := (le_dimensionalBlowup_apply_iff μ x hr ha measurableSet_ball).mp (hlo w hwV hwB)
    have hcenter : x + r • w = z := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    change ENNReal.ofReal (a*r^m) ≤ μ (blowUpMap x r ⁻¹' ball w η) at hmass
    rw [blowUpMap_preimage_ball' x w hr η, hcenter, mul_comm r η] at hmass
    exact hmass

end Preiss
