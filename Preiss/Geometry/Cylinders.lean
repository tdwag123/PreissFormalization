module

public import Preiss.Geometry.Projections
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def cylinder (V : Plane m n) (p : Euclidean n) (r : ℝ) : Set (Euclidean n) :=
  {y | dist (proj V y) p < r}

set_option maxHeartbeats 800000 in
theorem exists_unit_small_projection_of_avoids_cylinder (hm : 0 < m)
    (V W : Plane m n) (z p : Euclidean n) {ρ r : ℝ}
    (hp : p ∈ V.1) (hρ : 0 < ρ) (hr : 0 < r)
    (hd : dist (proj V z) p = ρ)
    (havoid : ∀ y : Euclidean n, y - z ∈ W.1 → y ∈ ball z r →
      y ∉ cylinder V p (ρ / 4)) :
    ∃ w : Euclidean n, w ∈ W.1 ∧ ‖w‖ = 1 ∧ ‖proj V w‖ ≤ 4 * ρ / r := by
  classical
  by_contra h
  push Not at h
  let T : W.1 →ₗ[ℝ] V.1 := V.1.orthogonalProjectionOnto.toLinearMap.comp W.1.subtype
  have hbound (v : W.1) (hv : v ≠ 0) : (4 * ρ / r) * ‖v‖ < ‖T v‖ := by
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hvcoe : (v : Euclidean n) ≠ 0 := fun hh ↦ hv (Subtype.ext hh)
    have hh := h (‖v‖⁻¹ • (v : Euclidean n)) (W.1.smul_mem _ v.property)
      (norm_smul_inv_norm hvcoe)
    have hproj : proj V (‖v‖⁻¹ • (v : Euclidean n)) = ‖v‖⁻¹ • (T v : Euclidean n) := by
      change V.1.starProjection (_ • _) = _
      rw [map_smul]
      rfl
    rw [hproj, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hvnorm.le] at hh
    have hh' : 4 * ρ / r < ‖T v‖ / ‖v‖ := by simpa only [div_eq_mul_inv, mul_comm, Submodule.norm_coe] using hh
    exact (lt_div_iff₀ hvnorm).mp hh'
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    by_contra hne
    have hh := hbound v hne
    have hTv : T v = 0 := hv
    rw [hTv, norm_zero] at hh
    have hnonneg : 0 ≤ (4 * ρ / r) * ‖v‖ := by positivity
    linarith
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (W.property.trans V.property.symm)).mp hinj
  have hmem : p - proj V z ∈ V.1 := V.1.sub_mem hp (V.1.orthogonalProjectionOnto z).property
  obtain ⟨v, hv⟩ := hsurj ⟨p - proj V z, hmem⟩
  have hprojv : proj V (v : Euclidean n) = p - proj V z := congrArg Subtype.val hv
  have hnormTv : ‖T v‖ = ρ := by
    rw [hv]
    change ‖p - proj V z‖ = ρ
    rw [← dist_eq_norm, dist_comm]
    exact hd
  have hvsmall : ‖v‖ < r := by
    by_cases hv0 : v = 0
    · simpa only [hv0, norm_zero] using hr
    · have hh := hbound v hv0
      rw [hnormTv] at hh
      have hh' := (div_lt_iff₀ hr).mp (show 4 * ρ * ‖v‖ / r < ρ by
        simpa only [div_mul_eq_mul_div] using hh)
      nlinarith
  apply havoid (z + (v : Euclidean n))
  · simpa only [add_sub_cancel_left] using v.property
  · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, Submodule.norm_coe] using hvsmall
  · change dist (proj V (z + (v : Euclidean n))) p < ρ / 4
    have heq : proj V (z + (v : Euclidean n)) = p := by
      change V.1.starProjection (z + (v : Euclidean n)) = p
      rw [map_add]
      change proj V z + proj V (v : Euclidean n) = p
      rw [hprojv]
      abel
    rw [heq, dist_self]
    positivity

theorem exists_unit_small_projection_of_empty_inner_cylinder (hm : 0 < m)
    (V W : Plane m n) (F : Set (Euclidean n)) (a z p : Euclidean n)
    {ρ σ β : ℝ} (hF : F.Nonempty) (hp : p ∈ V.1)
    (hρ : 0 < ρ) (hσ : 0 < σ) (hβ : 0 < β) (hβsmall : β < 1 / 8)
    (hρσ : ρ ≤ β * σ) (hz : z ∈ ball a (σ / 2))
    (hd : dist (proj V z) p = ρ)
    (happrox : ∀ y : Euclidean n, y - z ∈ W.1 →
      y ∈ ball z (ρ / (8 * β)) → infDist y F < ρ / 8)
    (hempty : Disjoint (F ∩ ball a σ) (cylinder V p (ρ / 2))) :
    ∃ w : Euclidean n, w ∈ W.1 ∧ ‖w‖ = 1 ∧ ‖proj V w‖ ≤ 32 * β := by
  have havoid : ∀ y : Euclidean n, y - z ∈ W.1 →
      y ∈ ball z (ρ / (8 * β)) → y ∉ cylinder V p (ρ / 4) := by
    intro y hyW hy hycyl
    obtain ⟨q, hqF, hyq⟩ := (infDist_lt_iff hF).mp (happrox y hyW hy)
    have hrσ : ρ / (8 * β) ≤ σ / 8 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have hρsmall : ρ < σ / 8 := lt_of_le_of_lt hρσ (by nlinarith)
    have hqa : q ∈ ball a σ := by
      have hh := dist_triangle4 q y z a
      rw [dist_comm q y] at hh
      have hyz : dist y z < ρ / (8 * β) := hy
      have hza : dist z a < σ / 2 := hz
      show dist q a < σ
      linarith
    have hqcyl : q ∈ cylinder V p (ρ / 2) := by
      have hlip : dist (proj V q) (proj V y) ≤ dist q y := by
        change dist (V.1.starProjection q) (V.1.starProjection y) ≤ dist q y
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact V.1.norm_starProjection_apply_le _
      have hh := dist_triangle (proj V q) (proj V y) p
      have hyc : dist (proj V y) p < ρ / 4 := hycyl
      rw [dist_comm q y] at hlip
      show dist (proj V q) p < ρ / 2
      linarith
    exact Set.disjoint_left.mp hempty ⟨hqF, hqa⟩ hqcyl
  obtain ⟨w, hw, hnorm, hproj⟩ := exists_unit_small_projection_of_avoids_cylinder
    hm V W z p hp hρ (show 0 < ρ / (8 * β) by positivity) hd havoid
  refine ⟨w, hw, hnorm, ?_⟩
  have heq : 4 * ρ / (ρ / (8 * β)) = 32 * β := by field_simp [hρ.ne', hβ.ne']; ring
  simpa only [heq] using hproj
end Preiss
