module
public import Preiss.Analysis.Grading
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}

theorem weightedGrading_inner_self (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (s : ℝ) (x : E) :
    inner ℝ (weightedGrading P s x) x =
      ∑ i, s ^ (i.val+1) * ‖P i x‖ ^ 2 := by
  simp only [weightedGrading, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, sum_inner, inner_smul_left, RCLike.conj_to_real]
  apply Finset.sum_congr rfl
  intro i _
  have hidem : P i (P i x) = P i x := congrArg (fun T : E →L[ℝ] E => T x) (hP.2.1 i)
  have hinner : inner ℝ (P i x) x = ‖P i x‖^2 := by
    calc
      _ = inner ℝ (P i (P i x)) x := by rw [hidem]
      _ = inner ℝ (P i x) (P i x) := hP.1 i (P i x) x
      _ = _ := real_inner_self_eq_norm_sq _
  rw [hinner]

theorem weightedGrading_inner_pos (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) {s : ℝ} (hs : 0 < s) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ (weightedGrading P s x) x := by
  classical
  have hex : ∃ i, P i x ≠ 0 := by
    by_contra! h
    have hsum := congrArg (fun T : E →L[ℝ] E => T x) hP.2.2.2
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.id_apply, h,
      Finset.sum_const_zero] at hsum
    exact hx hsum.symm
  obtain ⟨i,hi⟩ := hex
  rw [weightedGrading_inner_self P hP]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (pow_nonneg hs.le _) (sq_nonneg _)
  · exact ⟨i,Finset.mem_univ i,mul_pos (pow_pos hs _) (sq_pos_of_pos (norm_pos_iff.mpr hi))⟩

theorem weightedGrading_injective (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) {s : ℝ} (hs : 0 < s) :
    Function.Injective (weightedGrading P s) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  by_contra hne
  have h := weightedGrading_inner_pos P hP hs hne
  rw [hx, inner_zero_left] at h
  exact lt_irrefl _ h

theorem weightedGrading_inner_left_right (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (s : ℝ) (x y : E) :
    inner ℝ (weightedGrading P s x) y = inner ℝ x (weightedGrading P s y) := by
  simp only [weightedGrading, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real, hP.1]

theorem isCompl_weightedComplement (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) {s : ℝ} (hs : 0 < s) :
    IsCompl V (weightedComplement P V s) := by
  let B : LinearMap.BilinForm ℝ E := (innerₗ E).compl₂ (weightedGrading P s).toLinearMap
  have hB (x y : E) : B x y = inner ℝ x (weightedGrading P s y) := rfl
  have href : B.IsRefl := by
    intro x y hxy
    rw [hB] at hxy ⊢
    rw [← weightedGrading_inner_left_right P hP s x y, real_inner_comm] at hxy
    exact hxy
  have heq : B.orthogonal V = weightedComplement P V s := by
    ext x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    change (∀ y ∈ V, B y x = 0) ↔ weightedGrading P s x ∈ Vᗮ
    rw [Submodule.mem_orthogonal]
    simp only [hB]
  rw [← heq]
  apply (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint href).mpr
  rw [Submodule.disjoint_def]
  intro x hx horth
  by_contra hne
  have hz : B x x = 0 := horth x hx
  have hp := weightedGrading_inner_pos P hP hs hne
  rw [hB, ← weightedGrading_inner_left_right P hP s x x] at hz
  exact (ne_of_gt hp) hz

theorem analyticAt_weightedProjection_zero (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) :
    ∃ Q : ℝ → E →L[ℝ] E, AnalyticAt ℝ Q 0 ∧
      ∀ s : ℝ, 0 < s → IsCompl V (weightedComplement P V s) ∧
        (∀ x, Q s x ∈ V) ∧ (∀ v ∈ V, Q s v = v) ∧
        (∀ w ∈ weightedComplement P V s, Q s w = 0) := by
  sorry

end Preiss
