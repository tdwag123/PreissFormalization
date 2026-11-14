import Preiss.Analysis.QuadraticSpectralRigidity
import Preiss.Analysis.BilinearSpectrum
import Preiss.Geometry.SpectralPlaneEnergy
import Preiss.Uniform.GaussianCovariance
import Preiss.Uniform.ConicalMoments
import Preiss.Uniform.SupportProximity
import Preiss.Uniform.ConicalPlaneEnergy
import Mathlib.Tactic

/-! # Conical flatness gap -/

open MeasureTheory Metric Set
open scoped BigOperators
namespace Preiss
variable {n m : ℕ}

theorem conical_covariance_eq_projection_of_near_eigenvector
    (hm : 0 < m) (hmn : m ≤ n)
    (e : OrthonormalBasis (Fin n) ℝ (Euclidean n)) (α : Fin n → ℝ)
    (horder : Antitone α) (hα : ∀ i, 0 ≤ α i) (htrace : ∑ i, α i = (m : ℝ))
    (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, (∑ i, α i * (inner ℝ x (e i)) ^ 2) = ‖x‖ ^ 2)
    (i : Fin n) (hi : i.val + 1 = m) (δ : ℝ) (hδ : 0 < δ) (hδm : δ < 1 / (m : ℝ))
    (hnear : ∃ x ∈ S, dist x (e i) < δ) :
    ∀ j, α j = if j.val < m then 1 else 0 := by
  obtain ⟨x, hx, hnear⟩ := hnear
  exact ordered_quadratic_identity_rigid_of_near_basis_vector hm e α horder hα htrace
    i hi δ hδ hδm x (hS x hx) hnear

theorem conical_flatness_gap (hm : 0 < m) (hmn : m ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ν : Measure (Euclidean n)), IsUnitUniform m ν →
      IsConical m ν → (∃ V : Plane m n,
        (∫ z in ball 0 1, (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂ν) ≤ ε) →
      IsFlat m ν := by
  classical
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let δ : ℝ := 1 / (2 * (m : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδm : δ < 1 / (m : ℝ) := by
    dsimp [δ]
    exact one_div_lt_one_div_of_lt hmR (by linarith)
  obtain ⟨η, hη, hclose⟩ := dist_support_lt_of_small_gaussian_plane_energy hm hmn δ hδ
  let G : ℝ := Real.Gamma (((m : ℝ) + 2) / 2 + 1)
  have hG : 0 < G := Real.Gamma_pos_of_pos (by positivity)
  refine ⟨η / G, div_pos hη hG, ?_⟩
  intro μ hμ hc hsmall
  obtain ⟨V, hVenergy⟩ := hsmall
  let A := momentBilinear (gaussianMomentForm μ 2 1)
  obtain ⟨hpos, htrace, hsupp⟩ := conical_covariance_trace_support μ hm hμ hc
  have hApos (x : Euclidean n) : 0 ≤ A x x := by
    simpa only [A, momentBilinear_diag] using hpos x
  have hAsymm (x y : Euclidean n) : A x y = A y x :=
    momentBilinear_gaussianMomentForm_symmetric μ 1 x y
  obtain ⟨e, α, horder, hα, hαtrace, hdiag⟩ :=
    exists_ordered_spectral_representation (by simp : Module.finrank ℝ (Euclidean n) = n)
      A hAsymm hApos
  have hsum : ∑ j, α j = (m : ℝ) := hαtrace.trans htrace
  have hsupport (x : Euclidean n) (hx : x ∈ μ.support) :
      (∑ j, α j * (inner ℝ x (e j)) ^ 2) = ‖x‖ ^ 2 := by
    rw [← hdiag, show A x x = gaussianMomentForm μ 2 1 (fun _ => x) from momentBilinear_diag _ x]
    exact hsupp x hx
  let i : Fin n := ⟨m - 1, by omega⟩
  have hi : i.val + 1 = m := by dsimp [i]; omega
  have hkernel := integrable_gaussianMomentKernel μ hm hμ 2 1 zero_lt_one
  have hmass : 0 < gaussianMass μ 1 := by
    rw [gaussianMass_unitUniform μ hm hμ 1 zero_lt_one]
    simp only [Real.one_rpow, mul_one]
    exact Real.Gamma_pos_of_pos (by positivity)
  have hnorm : Integrable (fun z : Euclidean n => Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ 2) μ := by
    simpa only [one_mul, neg_mul, mul_comm] using
      integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ.1 1 (m : ℝ)
        (IsUnitUniform.hasPolynomialGrowthBound μ hμ) 2 1 zero_lt_one
  have hcov (v : Euclidean n) :
      (∫ z, Real.exp (-‖z‖ ^ 2) * (inner ℝ z v) ^ 2 ∂μ) =
        (gaussianMass μ 1 / 2) * ∑ j, α j * (inner ℝ v (e j)) ^ 2 := by
    rw [integral_gaussian_inner_sq_eq_momentBilinear μ hkernel hmass.ne']
    exact congrArg (fun t : ℝ => gaussianMass μ 1 / 2 * t) (hdiag v)
  obtain ⟨W, hWmem, hWdist, hWmin⟩ := exists_minimizing_plane_of_ordered_covariance
    μ (fun z => Real.exp (-‖z‖ ^ 2)) e α horder i hi (gaussianMass μ 1 / 2)
    (by positivity) hnorm (integrable_gaussian_inner_sq_of_integrable_momentKernel μ hkernel) hcov
  have hE : (∫ z, Real.exp (-‖z‖ ^ 2) *
      (infDist z (W.1 : Set (Euclidean n))) ^ 2 ∂μ) ≤ η := by
    apply (hWmin V).trans
    rw [conical_gaussian_planeEnergy_eq_ball μ hμ hc V]
    calc
      G * (∫ z in ball 0 1, (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ) ≤ G * (η/G) :=
        mul_le_mul_of_nonneg_left hVenergy hG.le
      _ = η := by field_simp
  have hnear := hclose μ hμ W hE (e i) (hWmem i (Finset.mem_Iic.mpr le_rfl))
    (e.norm_eq_one i).le
  obtain ⟨x, hx, hxe⟩ := (infDist_lt_iff (show μ.support.Nonempty from ⟨0, hμ.2.1⟩)).mp hnear
  have heq := conical_covariance_eq_projection_of_near_eigenvector hm hmn e α
    horder hα hsum μ.support hsupport i hi δ hδ hδm ⟨x, hx, by simpa only [dist_comm] using hxe⟩
  have hsub : μ.support ⊆ (W.1 : Set (Euclidean n)) := by
    intro z hz
    have hsz := hsupport z hz
    have hle (j : Fin n) : j.val < m ↔ j ≤ i := by
      change j.val < m ↔ j.val ≤ i.val
      omega
    have hsum' : (∑ j, α j * (inner ℝ z (e j)) ^ 2) =
        ∑ j ∈ Finset.Iic i, (inner ℝ z (e j)) ^ 2 := by
      simp_rw [heq, hle, ite_mul, one_mul, zero_mul]
      have hfilter : Finset.univ.filter (fun j : Fin n => j ≤ i) = Finset.Iic i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      rw [← Finset.sum_filter, hfilter]
    rw [hsum'] at hsz
    have hd : (infDist z (W.1 : Set (Euclidean n))) ^ 2 = 0 := by
      rw [hWdist, hsz, sub_self]
    apply (W.1.closed_of_finiteDimensional.mem_iff_infDist_zero ⟨0, W.1.zero_mem⟩).mpr
    exact eq_zero_of_pow_eq_zero hd
  rw [unitUniform_eq_flat_of_support_subset_plane hm μ hμ W hsub]
  exact isFlat_unitFlat W


end Preiss
