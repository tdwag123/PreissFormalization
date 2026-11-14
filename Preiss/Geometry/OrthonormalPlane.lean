module

public import Preiss.Geometry.Projections
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
open Metric Set
open scoped BigOperators
namespace Preiss

theorem infDist_sq_eq_norm_sq_sub_sum_orthonormalBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (x : E) :
    (infDist x (V : Set E)) ^ 2 = ‖x‖ ^ 2 - ∑ a, (inner ℝ x (b a : E)) ^ 2 := by
  have hs := b.sum_sq_inner_left (V.orthogonalProjectionOnto x)
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at hs
  change (∑ a, (inner ℝ x (b a : E)) ^ 2) = ‖V.starProjection x‖ ^ 2 at hs
  have hcomp : Vᗮ.starProjection x = x - V.starProjection x := by
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using V.starProjection_add_starProjection_orthogonal x
  have hp := V.norm_sq_eq_add_norm_sq_starProjection x
  rw [hcomp] at hp
  rw [infDist_submodule_eq_norm_sub_starProjection]
  linarith

theorem exists_plane_of_orthonormalBasis_finset {m n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ (Euclidean n)) (s : Finset (Fin n)) (hcard : s.card = m) :
    ∃ V : Plane m n, (∀ j ∈ s, e j ∈ V.1) ∧ ∀ x : Euclidean n,
      (infDist x (V.1 : Set (Euclidean n))) ^ 2 =
        ‖x‖ ^ 2 - ∑ j ∈ s, (inner ℝ x (e j)) ^ 2 := by
  classical
  let U : Submodule ℝ (Euclidean n) := Submodule.span ℝ (s.image e : Set (Euclidean n))
  let b : OrthonormalBasis s ℝ U := OrthonormalBasis.span e.orthonormal s
  have hdim : Module.finrank ℝ U = m :=
    (Module.finrank_eq_card_finset_basis b.toBasis).trans hcard
  refine ⟨⟨U, hdim⟩, ?_, ?_⟩
  · intro j hj
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  · intro x
    have h := infDist_sq_eq_norm_sq_sub_sum_orthonormalBasis U b x
    have hb (a : s) : (b a : Euclidean n) = e a :=
      OrthonormalBasis.span_apply e.orthonormal s a
    have hsum : (∑ a : s, (inner ℝ x (b a : Euclidean n)) ^ 2) =
        ∑ j ∈ s, (inner ℝ x (e j)) ^ 2 := by
      calc
        (∑ a : s, (inner ℝ x (b a : Euclidean n)) ^ 2) =
            ∑ a : s, (inner ℝ x (e a)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hb]
        _ = ∑ j ∈ s, (inner ℝ x (e j)) ^ 2 := Finset.sum_coe_sort s (fun j : Fin n => (inner ℝ x (e j)) ^ 2)
    rw [hsum] at h
    exact h

end Preiss
