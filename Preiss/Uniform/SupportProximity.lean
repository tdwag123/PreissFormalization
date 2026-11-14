import Preiss.Uniform.Compactness
import Preiss.Uniform.Classification
import Preiss.Uniform.GaussianPlaneEnergy
import Preiss.Geometry.PlaneTopology
import Preiss.Analysis.Vague.Support
import Preiss.Analysis.Vague.WeightedProjectionSupport
import Mathlib.Tactic.FunProp

/-! # Support proximity from small Gaussian plane energy -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {n m : ℕ}

theorem dist_support_lt_of_small_gaussian_plane_energy
    (hm : 0 < m) (hmn : m ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (μ : Measure (Euclidean n)), IsUnitUniform m μ →
      ∀ V : Plane m n,
      (∫ z, Real.exp (-‖z‖ ^ 2) * (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ) ≤ η →
      ∀ x ∈ V.1, ‖x‖ ≤ 1 → infDist x μ.support < δ := by
  classical
  by_contra hnot
  push_neg at hnot
  choose μ hμ V hE x hx hxn hfar using fun i : ℕ =>
    hnot (1 / ((i : ℝ) + 1)) (by positivity)
  obtain ⟨φ, ν, hφ, hν, hμν⟩ := exists_vague_subsequence_unitUniform μ hμ
  obtain ⟨W, ψ, hψ, hVW⟩ := exists_tendsto_planeProjection_subseq (fun i => V (φ i))
  obtain ⟨x₀, hx₀ball, ρ, hρ, hx₀⟩ :=
    (isCompact_closedBall (0 : Euclidean n) 1).tendsto_subseq
      (x := fun i => x (φ (ψ i))) (fun i => by
        simpa only [mem_closedBall, dist_zero_right] using hxn (φ (ψ i)))
  let κ : ℕ → ℕ := φ ∘ ψ ∘ ρ
  have hκ : StrictMono κ := hφ.comp (hψ.comp hρ)
  have hlim : Measure.WeaklyConverges (fun i => μ (κ i)) ν :=
    fun f => (hμν f).comp (hψ.comp hρ).tendsto_atTop
  have hP : Tendsto (fun i => planeProjection (V (κ i))) atTop (𝓝 (planeProjection W)) :=
    hVW.comp hρ.tendsto_atTop
  have hxx : Tendsto (fun i => x (κ i)) atTop (𝓝 x₀) := hx₀
  have heval : Continuous (fun u : (Euclidean n →L[ℝ] Euclidean n) × Euclidean n =>
      u.1 u.2) := by fun_prop
  have hproj := (heval.tendsto (planeProjection W, x₀)).comp (hP.prodMk_nhds hxx)
  have hfix (i : ℕ) : planeProjection (V (κ i)) (x (κ i)) = x (κ i) :=
    (V (κ i)).1.starProjection_eq_self_iff.mpr (hx (κ i))
  change Tendsto (fun i => planeProjection (V (κ i)) (x (κ i))) atTop
    (𝓝 (planeProjection W x₀)) at hproj
  simp only [hfix] at hproj
  have hxW : x₀ ∈ W.1 := W.1.starProjection_eq_self_iff.mp (tendsto_nhds_unique hproj hxx)
  have henergy : Tendsto (fun i => ∫ z, Real.exp (-‖z‖ ^ 2) *
      (infDist z ((V (κ i)).1 : Set (Euclidean n))) ^ 2 ∂μ (κ i)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => integral_nonneg fun z =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (fun i => hE (κ i))
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hκ.tendsto_atTop
  have hsupport : ν.support ⊆ (W.1 : Set (Euclidean n)) := by
    have hfixed := support_subset_fixedPoints_of_vague_of_weighted_projectionEnergy_tendsto_zero
      (fun z => Real.exp (-‖z‖ ^ 2)) (by fun_prop) (fun z => Real.exp_pos _)
      (fun i => μ (κ i)) ν (fun i => (hμ (κ i)).1) hν.1 hlim
      (fun i => planeProjection (V (κ i))) (planeProjection W) hP
      (fun i => by
        simpa only [infDist_submodule_eq_norm_sub_starProjection, planeProjection] using
          integrable_gaussian_planeEnergy_of_unitUniform (μ (κ i)) (hμ (κ i)) (V (κ i)))
      (by simpa only [infDist_submodule_eq_norm_sub_starProjection, planeProjection] using henergy)
    intro z hz
    exact W.1.starProjection_eq_self_iff.mp (hfixed hz)
  have hflat := unitUniform_eq_flat_of_support_subset_plane hm ν hν W hsupport
  have hxν : x₀ ∈ ν.support := by
    rw [hflat, unitFlat_support]
    exact hxW
  obtain ⟨y, hy, hyconv⟩ := exists_support_sequence_of_vague
    (fun i => μ (κ i)) ν (fun i => (hμ (κ i)).1) hν.1 hlim x₀ hxν
  have hdist : Tendsto (fun i => dist (x (κ i)) (y i)) atTop (𝓝 0) := by
    simpa only [dist_self] using hxx.dist hyconv
  obtain ⟨i, hi, hsmall⟩ := (hy.and (hdist.eventually (eventually_lt_nhds hδ))).exists
  exact (not_lt_of_ge (hfar (κ i))) ((infDist_le_dist_of_mem hi).trans_lt hsmall)

end Preiss
