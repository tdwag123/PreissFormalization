module

public import Preiss.Geometry.OrthonormalPlane
public import Preiss.Analysis.OrderedSpectralBound
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.SimpRw

@[expose] public section
open MeasureTheory Metric Set
open scoped BigOperators
namespace Preiss

theorem integral_weighted_planeEnergy_eq_sub_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (w : E → ℝ)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (hnorm : Integrable (fun z => w z * ‖z‖ ^ 2) μ)
    (hdir : ∀ v : E, Integrable (fun z => w z * (inner ℝ z v) ^ 2) μ) :
    (∫ z, w z * (infDist z (V : Set E)) ^ 2 ∂μ) =
      (∫ z, w z * ‖z‖ ^ 2 ∂μ) - ∑ a, ∫ z, w z * (inner ℝ z (b a : E)) ^ 2 ∂μ := by
  classical
  simp_rw [infDist_sq_eq_norm_sq_sub_sum_orthonormalBasis V b,
    mul_sub, Finset.mul_sum]
  rw [integral_sub hnorm (integrable_finset_sum _ (fun a _ => hdir (b a))),
    integral_finsetSum _ (fun a _ => hdir (b a))]

theorem exists_minimizing_plane_of_ordered_covariance {m n : ℕ}
    (μ : Measure (Euclidean n)) (w : Euclidean n → ℝ)
    (e : OrthonormalBasis (Fin n) ℝ (Euclidean n)) (α : Fin n → ℝ)
    (horder : Antitone α) (i : Fin n) (hi : i.val + 1 = m)
    (C : ℝ) (hC : 0 ≤ C)
    (hnorm : Integrable (fun z => w z * ‖z‖ ^ 2) μ)
    (hint : ∀ v : Euclidean n, Integrable (fun z => w z * (inner ℝ z v) ^ 2) μ)
    (hcov : ∀ v : Euclidean n, (∫ z, w z * (inner ℝ z v) ^ 2 ∂μ) =
      C * ∑ j, α j * (inner ℝ v (e j)) ^ 2) :
    ∃ W : Plane m n, (∀ j ∈ Finset.Iic i, e j ∈ W.1) ∧
      (∀ z, (infDist z (W.1 : Set (Euclidean n))) ^ 2 =
        ‖z‖ ^ 2 - ∑ j ∈ Finset.Iic i, (inner ℝ z (e j)) ^ 2) ∧
      ∀ V : Plane m n,
        (∫ z, w z * (infDist z (W.1 : Set (Euclidean n))) ^ 2 ∂μ) ≤
        (∫ z, w z * (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ) := by
  classical
  obtain ⟨W, hWmem, hWdist⟩ := exists_plane_of_orthonormalBasis_finset e (Finset.Iic i)
    ((Fin.card_Iic i).trans hi)
  refine ⟨W, hWmem, hWdist, ?_⟩
  intro V
  let b := stdOrthonormalBasis ℝ V.1
  have hv : Orthonormal ℝ (fun a => (b a : Euclidean n)) :=
    b.orthonormal.comp_linearIsometry V.1.subtypeₗᵢ
  have hbound := orthonormal_diagonal_sum_le_initial_sum e
    (fun a => (b a : Euclidean n)) hv (by simpa using V.property) α horder i hi
  have hWenergy : (∫ z, w z * (infDist z (W.1 : Set (Euclidean n))) ^ 2 ∂μ) =
      (∫ z, w z * ‖z‖ ^ 2 ∂μ) - C * ∑ j ∈ Finset.Iic i, α j := by
    simp_rw [hWdist, mul_sub, Finset.mul_sum]
    rw [integral_sub hnorm (integrable_finset_sum _ (fun j _ => hint (e j))),
      integral_finsetSum _ (fun j _ => hint (e j))]
    simp_rw [hcov]
    simp [e.inner_eq_ite, Finset.mul_sum]
  rw [hWenergy, integral_weighted_planeEnergy_eq_sub_sum μ w V.1 b hnorm hint]
  simp_rw [hcov]
  rw [← Finset.mul_sum]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hbound hC) _

end Preiss
