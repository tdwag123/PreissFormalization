import Preiss.Density.Defs
import FormalizingGMT.TangentMeasures.DensityIneqToTangentsLemmas2

/-! # Uniform pieces for finite upper density

The closed good-ball sets are reused from FormalizingGMT. No positive lower
density hypothesis is needed for this upper-bound localization.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem exists_closedBall_upper_bound_of_upperDensity_lt_top
    (μ : Measure (Euclidean n)) (x : Euclidean n)
    (h : dimensional_upper_density μ.toOuterMeasure (m : ℝ) x < ∞) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ m) := by
  obtain ⟨u, hu, hutop⟩ := exists_between h
  have hup : 0 < u.toReal :=
    ENNReal.toReal_pos (lt_of_le_of_lt bot_le hu).ne' hutop.ne
  obtain ⟨R, hR, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (eventually_lt_of_upper_density_lt (m : ℝ) x u hu)
  refine ⟨u.toReal * 2 ^ m, R, by positivity, hR, ?_⟩
  intro r hr hrR
  have hratio := hbound ⟨hr, hrR⟩
  change dimensional_density_ratio μ.toOuterMeasure (m : ℝ) x r < u at hratio
  rw [dimensional_density_ratio_closedBall _ _ _ hr.le] at hratio
  have hden : ENNReal.ofReal ((2 * r) ^ (m : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos (by positivity) _
  have hmul := (ENNReal.div_lt_iff (Or.inl hden) (Or.inl ENNReal.ofReal_ne_top)).mp hratio
  have heq : u * ENNReal.ofReal ((2 * r) ^ (m : ℝ)) =
      ENNReal.ofReal ((u.toReal * 2 ^ m) * r ^ m) := by
    calc
      _ = ENNReal.ofReal (u.toReal * (2 * r) ^ (m : ℝ)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hutop.ne]
      _ = _ := by rw [Real.rpow_natCast, mul_pow, mul_assoc]
  exact hmul.le.trans_eq heq

theorem exists_goodBallSet_mem_of_closedBall_upper_bound
    (μ : Measure (Euclidean n)) (x : Euclidean n) (C R : ℝ)
    (hR : 0 < R)
    (hbound : ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ m)) :
    ∃ j k : ℕ, x ∈ goodBallSet (m : ℝ) ((j : ℝ) + 1) k μ := by
  obtain ⟨j, hj⟩ := exists_nat_gt (C * 2 ^ m)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < R / 2 by positivity)
  refine ⟨j, k, ?_⟩
  intro y w hw hwk hxy
  have h2w : 2 * w < R := by linarith [hwk.trans hk]
  have hsub : closedBall y w ⊆ closedBall x (2 * w) := by
    intro z hz
    rw [mem_closedBall] at hz hxy ⊢
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ ≤ w + w := add_le_add hz (by simpa only [dist_comm] using hxy)
      _ = 2 * w := by ring
  calc
    μ (closedBall y w) ≤ μ (closedBall x (2 * w)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (C * (2 * w) ^ m) := hbound _ (by positivity) h2w
    _ ≤ ENNReal.ofReal (((j : ℝ) + 1) * w ^ (m : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_natCast, mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hw.le m)

theorem exists_goodBallSet_mem_of_upperDensity_lt_top
    (μ : Measure (Euclidean n)) (x : Euclidean n)
    (h : dimensional_upper_density μ.toOuterMeasure (m : ℝ) x < ∞) :
    ∃ j k : ℕ, x ∈ goodBallSet (m : ℝ) ((j : ℝ) + 1) k μ := by
  obtain ⟨C, R, _, hR, hbound⟩ := exists_closedBall_upper_bound_of_upperDensity_lt_top μ x h
  exact exists_goodBallSet_mem_of_closedBall_upper_bound μ x C R hR hbound

end Preiss
