module
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Tactic

/-! # Normal representatives and quadratic cylinder identities

These Hilbert-space lemmas are independent of measures and moment expansions.
-/

@[expose] public section
open InnerProductSpace
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_orthogonal_representative [CompleteSpace E]
    (K : Submodule ℝ E) (L : E →L[ℝ] ℝ) (hL : ∀ x ∈ K, L x = 0) :
    ∃ b : Kᗮ, ∀ x : E, L x = inner ℝ (b : E) x := by
  let b : E := (InnerProductSpace.toDual ℝ E).symm L
  have hb : b ∈ Kᗮ := by
    apply (K.mem_orthogonal' b).mpr
    intro x hx
    rw [show inner ℝ b x = L x from InnerProductSpace.toDual_symm_apply]
    exact hL x hx
  refine ⟨⟨b, hb⟩, ?_⟩
  intro x
  exact InnerProductSpace.toDual_symm_apply.symm

theorem normal_coordinates_of_quadratic_identity
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (b : Kᗮ) (x : E)
    (h : 2 * inner ℝ (b : E) x + ‖K.starProjection x‖ ^ 2 = ‖x‖ ^ 2) :
    ‖x - K.starProjection x‖ ^ 2 = 2 * inner ℝ (b : E) x ∧
      ‖x - K.starProjection x - (b : E)‖ = ‖b‖ ∧
      ‖x - K.starProjection x‖ ≤ 2 * ‖b‖ := by
  have hP := Submodule.norm_sq_eq_add_norm_sq_starProjection x K
  rw [K.starProjection_orthogonal_val] at hP
  have hq : ‖x - K.starProjection x‖ ^ 2 = 2 * inner ℝ (b : E) x := by linarith
  have hbP : inner ℝ (b : E) (K.starProjection x) = 0 :=
    K.inner_left_of_mem_orthogonal (K.orthogonalProjectionOnto x).property b.property
  have hbq : inner ℝ (x - K.starProjection x) (b : E) = inner ℝ (b : E) x := by
    rw [real_inner_comm, inner_sub_right, hbP, sub_zero]
  have hs := norm_sub_sq_real (x - K.starProjection x) (b : E)
  rw [hbq, hq] at hs
  have heq : ‖x - K.starProjection x - (b : E)‖ = ‖b‖ := by
    have h₁ := norm_nonneg (x - K.starProjection x - (b : E))
    have h₂ := norm_nonneg (b : E)
    change ‖x - K.starProjection x - (b : E)‖ = ‖(b : E)‖
    nlinarith
  refine ⟨hq, heq, ?_⟩
  have htri := norm_add_le (x - K.starProjection x - (b : E)) (b : E)
  rw [sub_add_cancel, heq] at htri
  change ‖x - K.starProjection x‖ ≤ 2 * ‖(b : E)‖
  change ‖x - K.starProjection x‖ ≤ ‖(b : E)‖ + ‖(b : E)‖ at htri
  linarith

end Preiss
