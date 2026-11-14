module

public import Preiss.Geometry.Projections
public import Preiss.Geometry.Cylinders
public import Preiss.Geometry.PlaneSlab
public import Preiss.Geometry.PlaneMeasure
public import Preiss.Geometry.Cones
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}


theorem projected_tube_subset_slab (V W : Plane m n) (a v : Euclidean n)
    {R η ε : ℝ} (hR : 0 ≤ R) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hv : v ∈ V.1) (hnorm : ‖v‖ = 1) (hproj : ‖proj W v‖ ≤ ε) :
    proj V '' (closedTube a W (η * R) ∩ closedBall a R) ⊆
      {z | z ∈ V.1 ∧ ‖z - proj V a‖ ≤ R ∧
        |inner ℝ v (z - proj V a)| ≤ (ε + η) * R} := by
  rintro z ⟨x, hx, rfl⟩
  have hxR : ‖x - a‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx.2
  have hres : ‖(x - a) - proj W (x - a)‖ ≤ η * R := by
    have heq : ‖(x - a) - proj W (x - a)‖ =
        infDist (x - a) (W.1 : Set (Euclidean n)) := by
      change ‖(x - a) - W.1.starProjection (x - a)‖ = _
      rw [Submodule.starProjection_minimal, infDist_eq_iInf]
      rfl
    rw [heq]
    exact hx.1
  have hinnerproj : |inner ℝ v (proj W (x - a))| ≤ ε * R := by
    have heq : inner ℝ v (proj W (x - a)) = inner ℝ (proj W v) (x - a) :=
      (W.1.inner_starProjection_left_eq_right v (x - a)).symm
    rw [heq]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hproj hxR (norm_nonneg _) hε)
  have hinnerres : |inner ℝ v ((x - a) - proj W (x - a))| ≤ η * R := by
    have hh := abs_real_inner_le_norm v ((x - a) - proj W (x - a))
    rw [hnorm, one_mul] at hh
    exact hh.trans hres
  have hinner : |inner ℝ v (x - a)| ≤ (ε + η) * R := by
    have heq : inner ℝ v (x - a) = inner ℝ v (proj W (x - a)) +
        inner ℝ v ((x - a) - proj W (x - a)) := by
      simp only [inner_sub_right]
      ring
    rw [heq]
    calc
      |inner ℝ v (proj W (x - a)) + inner ℝ v ((x - a) - proj W (x - a))| ≤
          |inner ℝ v (proj W (x - a))| + |inner ℝ v ((x - a) - proj W (x - a))| := abs_add_le _ _
      _ ≤ ε * R + η * R := add_le_add hinnerproj hinnerres
      _ = (ε + η) * R := by ring
  refine ⟨(V.1.orthogonalProjectionOnto x).property, ?_, ?_⟩
  · change ‖V.1.starProjection x - V.1.starProjection a‖ ≤ R
    rw [← map_sub]
    exact (V.1.norm_starProjection_apply_le _).trans hxR
  · have heq : inner ℝ v (proj V x - proj V a) = inner ℝ v (x - a) := by
      change inner ℝ v (V.1.starProjection x - V.1.starProjection a) = _
      rw [← map_sub, ← V.1.inner_starProjection_left_eq_right,
        V.1.starProjection_eq_self_iff.mpr hv]
    rw [heq]
    exact hinner

theorem hausdorffMeasure_projected_tube_le (m n : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V W : Plane m n) (a w : Euclidean n)
      (R η ε : ℝ), 0 < R → 0 ≤ η → 0 ≤ ε → w ∈ W.1 → ‖w‖ = 1 →
      ‖proj V w‖ ≤ ε →
      (Measure.hausdorffMeasure (m : ℝ)) (proj V '' (closedTube a W (η * R) ∩ closedBall a R)) ≤
        ENNReal.ofReal (C * (ε + η) * R ^ m) := by
  obtain ⟨C, hC, hslab⟩ := hausdorffMeasure_plane_slab_le m n hm
  refine ⟨C, hC, ?_⟩
  intro V W a w R η ε hR hη hε hw hnorm hproj
  obtain ⟨v, hv, hvnorm, hswap⟩ := exists_unit_small_projection_swapped V W w hε hw hnorm hproj
  have hsub := projected_tube_subset_slab V W a v hR.le hη hε hv hvnorm hswap
  exact (measure_mono hsub).trans (hslab V (proj V a) v R (ε + η)
    (V.1.orthogonalProjectionOnto a).property hv hvnorm hR.le (add_nonneg hε hη))

end Preiss
