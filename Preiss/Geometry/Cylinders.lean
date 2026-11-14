module

public import Preiss.Geometry.Projections
public import Preiss.Geometry.Cones
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

theorem exists_unit_small_projection_swapped (V W : Plane m n)
    (w : Euclidean n) {ε : ℝ} (hε : 0 ≤ ε) (hw : w ∈ W.1)
    (hnorm : ‖w‖ = 1) (hproj : ‖proj V w‖ ≤ ε) :
    ∃ v : Euclidean n, v ∈ V.1 ∧ ‖v‖ = 1 ∧ ‖proj W v‖ ≤ ε := by
  classical
  let S : V.1 →ₗ[ℝ] W.1 := W.1.orthogonalProjectionOnto.toLinearMap.comp V.1.subtype
  have hnormalize (v : V.1) :
      ‖proj W (‖v‖⁻¹ • (v : Euclidean n))‖ = ‖S v‖ / ‖v‖ := by
    have heq : proj W (‖v‖⁻¹ • (v : Euclidean n)) = ‖v‖⁻¹ • (S v : Euclidean n) := by
      change W.1.starProjection (_ • _) = _
      rw [map_smul]
      rfl
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      Submodule.norm_coe, div_eq_mul_inv, mul_comm]
  by_cases hS : Function.Injective S
  · have hsurj : Function.Surjective S :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (V.property.trans W.property.symm)).mp hS
    obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have hSv : proj W (v : Euclidean n) = w := congrArg Subtype.val hv
    have hnormS : ‖S v‖ = 1 := by rw [hv]; exact hnorm
    have hvne : v ≠ 0 := by
      intro hv0
      rw [hv0, map_zero, norm_zero] at hnormS
      norm_num at hnormS
    have hvcoe : (v : Euclidean n) ≠ 0 := fun hh ↦ hvne (Subtype.ext hh)
    have hinner : inner ℝ (v : Euclidean n) w = 1 := by
      have hh := W.1.starProjection_inner_eq_zero (v : Euclidean n) w hw
      change inner ℝ ((v : Euclidean n) - proj W (v : Euclidean n)) w = 0 at hh
      rw [inner_sub_left, hSv, real_inner_self_eq_norm_sq, hnorm] at hh
      norm_num at hh
      linarith
    have hinner' : inner ℝ (v : Euclidean n) (proj V w) = 1 := by
      have hh := V.1.inner_starProjection_left_eq_right (v : Euclidean n) w
      rw [V.1.starProjection_eq_self_iff.mpr v.property] at hh
      change inner ℝ (v : Euclidean n) w = inner ℝ (v : Euclidean n) (proj V w) at hh
      rw [← hh]
      exact hinner
    have hbound : 1 ≤ ‖v‖ * ε := by
      calc
        1 = inner ℝ (v : Euclidean n) (proj V w) := hinner'.symm
        _ ≤ ‖(v : Euclidean n)‖ * ‖proj V w‖ := real_inner_le_norm _ _
        _ ≤ ‖v‖ * ε := by
          rw [Submodule.norm_coe]
          exact mul_le_mul_of_nonneg_left hproj (norm_nonneg v)
    refine ⟨‖v‖⁻¹ • (v : Euclidean n), V.1.smul_mem _ v.property, norm_smul_inv_norm hvcoe, ?_⟩
    rw [hnormalize, hnormS]
    apply (div_le_iff₀ (norm_pos_iff.mpr hvne)).mpr
    simpa only [mul_comm] using hbound
  · have hker : S.ker ≠ ⊥ := fun hh ↦ hS (LinearMap.ker_eq_bot.mp hh)
    obtain ⟨v, hvker, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hvcoe : (v : Euclidean n) ≠ 0 := fun hh ↦ hvne (Subtype.ext hh)
    refine ⟨‖v‖⁻¹ • (v : Euclidean n), V.1.smul_mem _ v.property, norm_smul_inv_norm hvcoe, ?_⟩
    rw [hnormalize, show S v = 0 from hvker, norm_zero, zero_div]
    exact hε

theorem exists_unit_small_projection_of_near_plane (V W : Plane m n)
    (y : Euclidean n) {ε τ : ℝ} (hy : y ≠ 0) (hε : 0 ≤ ε)
    (hτ : 0 ≤ τ) (hτmax : τ ≤ 1 / 2)
    (hnear : infDist y (W.1 : Set (Euclidean n)) ≤ τ * ‖y‖)
    (hproj : ‖proj V y‖ ≤ ε * ‖y‖) :
    ∃ w : Euclidean n, w ∈ W.1 ∧ ‖w‖ = 1 ∧ ‖proj V w‖ ≤ 2 * (ε + τ) := by
  let u := proj W y
  have hres : ‖y - u‖ ≤ τ * ‖y‖ := by
    have heq : ‖y - u‖ = infDist y (W.1 : Set (Euclidean n)) := by
      change ‖y - W.1.starProjection y‖ = _
      rw [Submodule.starProjection_minimal, infDist_eq_iInf]
      rfl
    rwa [heq]
  have hnormy : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hhalf : ‖y‖ / 2 ≤ ‖u‖ := by
    have hh : ‖y‖ ≤ ‖y - u‖ + ‖u‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y - u) u
    have hh' := mul_le_mul_of_nonneg_right hτmax (norm_nonneg y)
    linarith
  have hu : 0 < ‖u‖ := lt_of_lt_of_le (by positivity) hhalf
  have hunonzero : u ≠ 0 := norm_pos_iff.mp hu
  have hVdiff : ‖proj V u - proj V y‖ ≤ τ * ‖y‖ := by
    change ‖V.1.starProjection u - V.1.starProjection y‖ ≤ _
    rw [← map_sub]
    apply (V.1.norm_starProjection_apply_le _).trans
    rwa [norm_sub_rev]
  have hVu : ‖proj V u‖ ≤ (ε + τ) * ‖y‖ := by
    have hh : ‖proj V u‖ ≤ ‖proj V u - proj V y‖ + ‖proj V y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (proj V u - proj V y) (proj V y)
    nlinarith
  refine ⟨‖u‖⁻¹ • u, W.1.smul_mem _ (W.1.orthogonalProjectionOnto y).property,
    norm_smul_inv_norm hunonzero, ?_⟩
  have heq : proj V (‖u‖⁻¹ • u) = ‖u‖⁻¹ • proj V u := by
    change V.1.starProjection (_ • _) = _
    rw [map_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hu.le]
  have hfrac : ‖proj V u‖ / ‖u‖ ≤ 2 * (ε + τ) := by
    apply (div_le_iff₀ hu).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (add_nonneg hε hτ)
    nlinarith
  simpa only [div_eq_mul_inv, mul_comm] using hfrac

theorem norm_projection_lt_of_outside_cone (V : Plane m n) (a b : Euclidean n)
    {ε : ℝ} (hε : 0 < ε) (houtside : b ∉ cone a V (1 / ε)) :
    b - a ≠ 0 ∧ ‖proj V (b - a)‖ < ε * ‖b - a‖ := by
  have hlt : (1 / ε) * ‖proj V (b - a)‖ < ‖(b - a) - proj V (b - a)‖ :=
    lt_of_not_ge houtside
  have hres : ‖(b - a) - proj V (b - a)‖ ≤ ‖b - a‖ := by
    have heq : ‖(b - a) - proj V (b - a)‖ = infDist (b - a) (V.1 : Set (Euclidean n)) := by
      change ‖(b - a) - V.1.starProjection (b - a)‖ = _
      rw [Submodule.starProjection_minimal, infDist_eq_iInf]
      rfl
    rw [heq]
    simpa only [dist_zero_right] using (infDist_le_dist_of_mem (x := b - a) V.1.zero_mem)
  have hfrac : ‖proj V (b - a)‖ / ε < ‖b - a‖ := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hlt.trans_le hres
  have hh : ‖proj V (b - a)‖ < ε * ‖b - a‖ := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hfrac
  refine ⟨?_, hh⟩
  intro heq
  rw [heq, norm_zero, mul_zero] at hh
  exact not_lt_of_ge (norm_nonneg _) hh
end Preiss
