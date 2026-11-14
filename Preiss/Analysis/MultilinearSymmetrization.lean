module
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Data.Fintype.Perm

@[expose] public section
open scoped BigOperators

namespace Preiss
section Symmetrization
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def symmetricContinuousMultilinearSubmodule :
    Submodule ℝ (ContinuousMultilinearMap ℝ (fun _ : ι => E) F) where
  carrier := {A | ∀ (σ : Equiv.Perm ι) (u : ι → E), A (u ∘ σ) = A u}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB σ u
    simp only [ContinuousMultilinearMap.add_apply]
    rw [hA σ u,hB σ u]
  smul_mem' := by
    intro c A hA σ u
    simp only [ContinuousMultilinearMap.smul_apply]
    rw [hA σ u]

noncomputable def symmetrizeContinuousMultilinearMap
    (A : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : ι => E) F := by
  classical
  exact (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm ι, A.domDomCongr σ

theorem symmetrizeContinuousMultilinearMap_apply_perm
    (A : ContinuousMultilinearMap ℝ (fun _ : ι => E) F)
    (τ : Equiv.Perm ι) (u : ι → E) :
    symmetrizeContinuousMultilinearMap A (u ∘ τ) = symmetrizeContinuousMultilinearMap A u := by
  classical
  simp only [symmetrizeContinuousMultilinearMap, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)

theorem symmetrizeContinuousMultilinearMap_eq_self
    (A : ContinuousMultilinearMap ℝ (fun _ : ι => E) F)
    (hA : ∀ (σ : Equiv.Perm ι) (u : ι → E), A (u ∘ σ) = A u) :
    symmetrizeContinuousMultilinearMap A = A := by
  classical
  ext u
  have hcard : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hA' (σ : Equiv.Perm ι) : A (fun i => u (σ i)) = A u := hA σ u
  simp only [symmetrizeContinuousMultilinearMap, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.domDomCongr_apply,
    hA', Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem symmetrizeContinuousMultilinearMap_diagonal
    (A : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) (x : E) :
    symmetrizeContinuousMultilinearMap A (fun _ => x) = A (fun _ => x) := by
  classical
  have hcard : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [symmetrizeContinuousMultilinearMap, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_def, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
theorem comp_symmetrizeContinuousMultilinearMap
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : F →L[ℝ] G) (A : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) :
    T.compContinuousMultilinearMap (symmetrizeContinuousMultilinearMap A) =
      symmetrizeContinuousMultilinearMap (T.compContinuousMultilinearMap A) := by
  classical
  ext u
  simp only [symmetrizeContinuousMultilinearMap,ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.sum_apply,ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,Function.comp_apply,map_smul,map_sum]

end Symmetrization
end Preiss
