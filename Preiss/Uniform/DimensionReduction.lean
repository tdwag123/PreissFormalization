import Preiss.Uniform.GMTAdapters
import Preiss.Uniform.TangentExistence
import Preiss.Tangent.Basic
import Preiss.Geometry.PlaneEmbedding
import Preiss.Uniform.Transport
import Preiss.Tangent.ScalingOrbit
import FormalizingGMT.MarstrandTheorem

/-! # Uniform dimension reduction retaining tangent witnesses

The hyperplane obtained after half-space reduction can have a different normal.
The equality-or-tangent alternative is retained for the scaling-orbit induction.
-/

open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- A02: retain the point, tangent relation, normal and exact unit normalization. -/
theorem exists_halfSpace_dimensionalTangent (hm : 0 < m)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hproper : ν.support ≠ Set.univ) :
    ∃ (y e : Euclidean n) (ξ : Measure (Euclidean n)), y ∈ ν.support ∧ e ≠ 0 ∧
      IsDimensionalTangent m ν ξ y ∧ IsUnitUniform m ξ ∧
      ξ.support ⊆ {z | 0 ≤ inner ℝ z e} := by
  have hreg := hν.1
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem _).1 hproper
  have hsptne : ν.support.Nonempty := ⟨0, hν.2.1⟩
  obtain ⟨y, hy, hdist⟩ := Measure.isClosed_support.exists_infDist_eq_dist hsptne z
  have hd : 0 < dist z y := by
    rw [← hdist]
    exact (Measure.isClosed_support.notMem_iff_infDist_pos hsptne).1 hz
  have hhole : ∀ p, dist p z < dist z y → p ∉ ν.support := by
    intro p hp
    apply Metric.notMem_of_dist_lt_infDist (x := z)
    rw [hdist, dist_comm]
    exact hp
  set e := y - z with he_def
  have hnorm_e : ‖e‖ = dist z y := by rw [he_def, ← dist_eq_norm, dist_comm]
  have he : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm_e
    linarith
  obtain ⟨lam, htan, hlam⟩ := exists_unitUniform_dimensionalTangent ν hν y hy
  refine ⟨y, e, lam, hy, he, htan, hlam, ?_⟩
  intro x hx
  by_contra hneg
  simp only [mem_ofPred_eq, not_le] at hneg
  set η := -inner ℝ x e with hη
  have hηpos : 0 < η := by linarith
  have henorm : 0 < ‖e‖ := norm_pos_iff.2 he
  set ε := η / (2 * ‖e‖) with hε
  have hεpos : 0 < ε := by positivity
  set M := ‖x‖ + ε with hM
  have hMnn : 0 ≤ M := by positivity
  have hzero : lam (ball x ε) = 0 := by
    refine SUniformAux.measure_open_eq_zero_of_isTangentMeasure hreg htan.isTangentMeasure isOpen_ball
      ⟨η / (M ^ 2 + 1), by positivity, fun r hr hrρ p hp hpG ↦ ?_⟩
    set w := blowUpMap y r p with hw
    have hp_eq : p - z = e + r • w := by
      rw [hw, blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, he_def]
      abel
    have hwx : ‖w - x‖ < ε := by rw [← dist_eq_norm]; exact hpG
    have hwM : ‖w‖ ≤ M := by
      have := norm_le_norm_add_norm_sub' w x
      rw [hM]
      linarith
    have hinner : inner ℝ e w ≤ -η / 2 := by
      have h1 : inner ℝ e w = inner ℝ x e + inner ℝ (w - x) e := by
        have k1 := inner_sub_left (𝕜 := ℝ) w x e
        have k2 := real_inner_comm e w
        linarith
      have h2 : inner ℝ (w - x) e ≤ ‖w - x‖ * ‖e‖ := real_inner_le_norm _ _
      have h3 : ‖w - x‖ * ‖e‖ ≤ ε * ‖e‖ := by gcongr
      have h4 : ε * ‖e‖ = η / 2 := by rw [hε]; field_simp
      linarith
    have hsq : ‖p - z‖ ^ 2 < (dist z y) ^ 2 := by
      rw [hp_eq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, hnorm_e]
      have hrM : r * M ^ 2 < η := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < M ^ 2 + 1)).1 hrρ
        nlinarith
      have hw2 : ‖w‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwM 2
      have k1 : r * inner ℝ e w ≤ r * (-η / 2) := mul_le_mul_of_nonneg_left hinner hr.le
      have k2 : (r * ‖w‖) ^ 2 ≤ r ^ 2 * M ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hw2 (sq_nonneg r)
      have k3 : r ^ 2 * M ^ 2 < r * η := by
        have := mul_lt_mul_of_pos_left hrM hr
        nlinarith
      linarith
    have hlt : dist p z < dist z y := by
      rw [dist_eq_norm]
      exact lt_of_pow_lt_pow_left₀ 2 hd.le hsq
    exact hhole p hlt hp
  exact ((Measure.mem_support_iff_forall x).1 hx _ (ball_mem_nhds x hεpos)).ne' hzero

/-- A03: w need not equal the original half-space normal e. -/
theorem exists_hyperplane_eq_or_dimensionalTangent (hm : 0 < m)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (e : Euclidean n) (he : e ≠ 0)
    (hhalf : ν.support ⊆ {z | 0 ≤ inner ℝ z e}) :
    ∃ (w : Euclidean n) (ξ : Measure (Euclidean n)), w ≠ 0 ∧
      IsUnitUniform m ξ ∧ ξ.support ⊆ {z | inner ℝ z w = 0} ∧
      (ξ = ν ∨ IsDimensionalTangent m ν ξ 0) := by
  have hu := ((isUnitUniform_iff hm ν).mp hν).1
  letI : ν.Regular := hν.1
  by_cases hA : ∀ r : ℝ, 0 < r → ∫ z in closedBall (0 : Euclidean n) r, z ∂ν = 0
  · refine ⟨e, ν, he, hν, ?_, Or.inl rfl⟩
    apply SUniformAux.support_subset_of_integral_inner_eq_zero hu hhalf
    intro r hr
    have hi : Integrable (fun z ↦ z) (ν.restrict (closedBall 0 r)) :=
      continuous_id.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    have := integral_inner (𝕜 := ℝ) hi e
    simp_rw [real_inner_comm e]
    rw [this, hA r hr, inner_zero_right]
  · push Not at hA
    obtain ⟨r, hr, hw⟩ := hA
    obtain ⟨C, hC, hest⟩ := SUniformAux.abs_inner_integral_le hu hν.2.1 hr
    obtain ⟨ξ, htan, hξ⟩ := exists_unitUniform_dimensionalTangent ν hν 0 hν.2.1
    exact ⟨_, ξ, hw, hξ,
      SUniformAux.support_tangent_subset_of_estimate hu hC hr hest htan.isTangentMeasure,
      Or.inr htan⟩

/-- A06b: retain the isometric pushforward's membership in the bounded-radius
support-centered scaling orbit closure. -/
theorem uniform_dimension_reduction (hm : 0 < m) (hmn : m < n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ (L : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n)
      (ξ : Measure (Euclidean (n - 1))), IsUnitUniform m ξ ∧
      IsUniformPseudotangent m ν (ξ.map L) := by
  have hproper : ν.support ≠ Set.univ := by
    apply support_ne_univ_of_lower_growth (s := (m : ℝ)) (by exact_mod_cast hmn)
      ν hν.1 (c := 1) zero_lt_one
    intro x hx r hr
    rw [hν.2.2 x hx r hr, one_mul, Real.rpow_natCast]
  obtain ⟨y, e, κ, hy, he, hκtan, hκ, hhalf⟩ :=
    exists_halfSpace_dimensionalTangent hm ν hν hproper
  obtain ⟨w, ζ, hw, hζ, hhyper, halt⟩ :=
    exists_hyperplane_eq_or_dimensionalTangent hm κ hκ e he hhalf
  have horbit : IsUniformPseudotangent m ν ζ := by
    rcases halt with rfl | htan
    · exact hκtan.isUniformPseudotangent hy
    · exact uniformPseudotangent_trans ν κ ζ hν (hκtan.isUniformPseudotangent hy)
        (htan.isUniformPseudotangent hκ.2.1)
  have hn : 1 ≤ n := by omega
  letI : Fact (Module.finrank ℝ (Euclidean n) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let V : Plane (n - 1) n := ⟨(ℝ ∙ w)ᗮ, Submodule.finrank_orthogonal_span_singleton hw⟩
  obtain ⟨L, hLV⟩ := exists_linearIsometry_range_plane V
  have hsupp : ζ.support ⊆ Set.range L := by
    rw [hLV]
    intro z hz
    change z ∈ (ℝ ∙ w)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact hhyper hz
  obtain ⟨ξ, hξ, hmap, _, _⟩ := uniform_hyperplane_transport L ζ hζ hsupp
  exact ⟨L, ξ, hξ, by rwa [hmap]⟩

end Preiss
