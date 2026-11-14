import Preiss.Uniform.Compactness
import Preiss.Uniform.Classification
import Preiss.Analysis.Vague.Support
import Preiss.Geometry.Projections
import Mathlib.Tactic
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem exists_plane_to_support_bound_of_bounded_normal_coordinates
    (hm : 0 < m) (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ)
    (V : Plane m n) {M : ℝ} (hM : 0 ≤ M)
    (htube : ∀ x ∈ μ.support, ‖x - proj V x‖ ≤ M) :
    ∃ R : ℝ, 0 < R ∧ ∀ v : V.1, infDist (v : Euclidean n) μ.support < R := by
  classical
  by_contra hnot
  push_neg at hnot
  choose v hv using fun i : ℕ => hnot ((i : ℝ) + 1) (by positivity)
  have hne : μ.support.Nonempty := ⟨0, hμ.2.1⟩
  choose a ha hdist using fun i =>
    (Measure.isClosed_support (μ := μ)).exists_infDist_eq_dist hne (v i : Euclidean n)
  let r : ℕ → ℝ := fun i => infDist (v i : Euclidean n) μ.support
  have hr (i : ℕ) : 0 < r i := by
    have h := hv i
    dsimp [r]
    linarith [Nat.cast_nonneg (R := ℝ) i]
  have hr∞ : Tendsto r atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop N] with i hi
    have hNi : (N : ℝ) ≤ i := by exact_mod_cast hi
    have hh := hv i
    change b ≤ infDist (v i : Euclidean n) μ.support
    linarith
  let c : ℕ → Euclidean n := fun i => (r i)⁻¹ • ((v i : Euclidean n) - a i)
  have hc (i : ℕ) : ‖c i‖ = 1 := by
    have hd : ‖(v i : Euclidean n) - a i‖ = r i := by
      simpa only [dist_eq_norm] using (hdist i).symm
    dsimp only [c]
    rw [norm_smul, Real.norm_of_pos (inv_pos.mpr (hr i)), hd, inv_mul_cancel₀ (hr i).ne']
  let τ : ℕ → Measure (Euclidean n) := fun i => dimensionalBlowup m μ (a i) (r i)
  have hτ (i : ℕ) : IsUnitUniform m (τ i) := isUnitUniform_dimensionalBlowup μ hμ (a i) (ha i) (hr i)
  let Q : Euclidean n →L[ℝ] Euclidean n := ContinuousLinearMap.id ℝ _ - V.1.starProjection
  have hQa (i : ℕ) : ‖Q (a i)‖ ≤ M := htube (a i) (ha i)
  have hscale (i : ℕ) (z : Euclidean n) (hz : ‖Q z‖ ≤ M) :
      ‖Q ((r i)⁻¹ • (z - a i))‖ ≤ 2 * M / r i := by
    rw [map_smul, map_sub, norm_smul, Real.norm_of_pos (inv_pos.mpr (hr i))]
    calc (r i)⁻¹ * ‖Q z - Q (a i)‖ ≤ (r i)⁻¹ * (‖Q z‖ + ‖Q (a i)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (hr i).le)
      _ ≤ (r i)⁻¹ * (M + M) :=
        mul_le_mul_of_nonneg_left (add_le_add hz (hQa i)) (inv_nonneg.mpr (hr i).le)
      _ = 2 * M / r i := by ring
  have hτtube (i : ℕ) (y : Euclidean n) (hy : y ∈ (τ i).support) :
      ‖Q y‖ ≤ 2 * M / r i := by
    change y ∈ (dimensionalBlowup m μ (a i) (r i)).support at hy
    rw [dimensionalBlowup_support μ (a i) (hr i)] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hscale i z (htube z hz)
  have hctube (i : ℕ) : ‖Q (c i)‖ ≤ 2 * M / r i := by
    apply hscale
    have hzero : Q (v i : Euclidean n) = 0 := by
      change (v i : Euclidean n) - V.1.starProjection (v i) = 0
      rw [V.1.starProjection_mem_subspace_eq_self, sub_self]
    rwa [hzero, norm_zero]
  have hhole (i : ℕ) (y : Euclidean n) (hy : y ∈ (τ i).support) : 1 ≤ dist (c i) y := by
    change y ∈ (dimensionalBlowup m μ (a i) (r i)).support at hy
    rw [dimensionalBlowup_support μ (a i) (hr i)] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hfar : r i ≤ dist (v i : Euclidean n) z := infDist_le_dist_of_mem hz
    calc 1 = (r i)⁻¹ * r i := (inv_mul_cancel₀ (hr i).ne').symm
      _ ≤ (r i)⁻¹ * dist (v i : Euclidean n) z := mul_le_mul_of_nonneg_left hfar (inv_nonneg.mpr (hr i).le)
      _ = dist (c i) ((r i)⁻¹ • (z - a i)) := by
        dsimp only [c]
        rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_pos (inv_pos.mpr (hr i)), dist_eq_norm]
        congr 2
        abel
  obtain ⟨w, _, ψ, hψ, hcψ⟩ :=
    (isCompact_closedBall (0 : Euclidean n) 1).tendsto_subseq (x := c)
      (fun i => by simpa only [mem_closedBall, dist_zero_right, hc i])
  obtain ⟨φ, ν, hφ, hν, hlim⟩ := exists_vague_subsequence_unitUniform (fun i => τ (ψ i)) (fun i => hτ (ψ i))
  let κ : ℕ → ℕ := ψ ∘ φ
  have hκ : StrictMono κ := hψ.comp hφ
  have hclim : Tendsto (fun i => c (κ i)) atTop (𝓝 w) := hcψ.comp hφ.tendsto_atTop
  have hvlim : Tendsto (fun i => 2 * M / r (κ i)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * M) atTop (𝓝 (2 * M))).mul
        (tendsto_inv_atTop_zero.comp (hr∞.comp hκ.tendsto_atTop)))
  have hmem (y : ℕ → Euclidean n) (z : Euclidean n) (hy : Tendsto y atTop (𝓝 z))
      (hb : ∀ᶠ i in atTop, ‖Q (y i)‖ ≤ 2 * M / r (κ i)) : z ∈ V.1 := by
    have hzlim : Tendsto (fun i => ‖Q (y i)‖) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) hb hvlim
    have hz : Q z = 0 := norm_eq_zero.mp
      (tendsto_nhds_unique (((Q.continuous.tendsto z).comp hy).norm) hzlim)
    change z - V.1.starProjection z = 0 at hz
    have hfix : V.1.starProjection z = z := (sub_eq_zero.mp hz).symm
    exact V.1.starProjection_eq_self_iff.mp hfix
  have hνplane : ν.support ⊆ (V.1 : Set (Euclidean n)) := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := exists_support_sequence_of_vague (fun i => τ (κ i)) ν
      (fun i => (hτ (κ i)).1) hν.1 hlim z hz
    apply hmem y z hyz
    filter_upwards [hy] with i hi
    exact hτtube (κ i) (y i) hi
  have hνflat : ν = unitFlat V := unitUniform_eq_flat_of_support_subset_plane hm ν hν V hνplane
  have hw : w ∈ ν.support := by
    rw [hνflat, unitFlat_support]
    exact hmem (fun i => c (κ i)) w hclim (Eventually.of_forall fun i => hctube (κ i))
  obtain ⟨y, hy, hyw⟩ := exists_support_sequence_of_vague (fun i => τ (κ i)) ν
    (fun i => (hτ (κ i)).1) hν.1 hlim w hw
  have hzero : Tendsto (fun i => dist (c (κ i)) (y i)) atTop (𝓝 0) := by simpa using hclim.dist hyw
  have hbad : (1 : ℝ) ≤ 0 := le_of_tendsto hzero (by
    filter_upwards [hy] with i hi
    exact hhole (κ i) (y i) hi)
  norm_num at hbad

#print axioms exists_plane_to_support_bound_of_bounded_normal_coordinates
end Preiss
