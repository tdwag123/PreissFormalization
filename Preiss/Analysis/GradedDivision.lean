module
public import Preiss.Analysis.Grading
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Tactic

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Division
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {N : ℕ}

noncomputable def dividedGradingMap (D : Fin N → F →L[ℝ] F)
    (R : Fin N → E →L[ℝ] F) (s : ℝ) : E →L[ℝ] F :=
  ∑ i, ∑ j, if i.val ≤ j.val then
    s ^ (j.val - i.val) • (D i).comp (R j) else 0

theorem dividedGradingMap_row (D : Fin N → F →L[ℝ] F)
    (hD : IsOrthogonalGrading D) (R : Fin N → E →L[ℝ] F) (s : ℝ)
    (k : Fin N) (x : E) :
    D k (dividedGradingMap D R s x) =
      ∑ j, if k.val ≤ j.val then s ^ (j.val - k.val) • D k (R j x) else 0 := by
  classical
  simp only [dividedGradingMap, ContinuousLinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single k]
  · apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]
      exact congrArg (fun T : F →L[ℝ] F => s ^ (j.val - k.val) • T (R j x)) (hD.2.1 k)
    · simp
  · intro i _ hik
    apply Finset.sum_eq_zero
    intro j _
    split_ifs
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]
      have hz : D k (D i (R j x)) = 0 :=
        congrArg (fun T : F →L[ℝ] F => T (R j x)) (hD.2.2.1 k i (Ne.symm hik))
      rw [hz, smul_zero]
    · simp
  · simp

theorem weightedGrading_comp_dividedGradingMap (D : Fin N → F →L[ℝ] F)
    (hD : IsOrthogonalGrading D) (R : Fin N → E →L[ℝ] F)
    (hR : ∀ i j : Fin N, j.val < i.val → (D i).comp (R j) = 0) (s : ℝ) :
    (weightedGrading D s).comp (dividedGradingMap D R s) =
      ∑ j, s ^ (j.val+1) • R j := by
  classical
  ext x
  simp only [ContinuousLinearMap.comp_apply, weightedGrading,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    dividedGradingMap_row D hD, Finset.smul_sum]
  have hterm (i j : Fin N) :
      s ^ (i.val+1) • (if i.val ≤ j.val then
        s ^ (j.val-i.val) • D i (R j x) else 0) =
        s ^ (j.val+1) • D i (R j x) := by
    split_ifs with hij
    · rw [smul_smul, ← pow_add]
      congr 2
      omega
    · have hz : D i (R j x) = 0 :=
        congrArg (fun T : E →L[ℝ] F => T x) (hR i j (by omega))
      simp [hz]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.smul_sum]
  have hsum := congrArg (fun T : F →L[ℝ] F => T (R j x)) hD.2.2.2
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun y : F => s ^ (j.val+1) • y) hsum

theorem dividedGradingMap_zero (D : Fin N → F →L[ℝ] F)
    (R : Fin N → E →L[ℝ] F) :
    dividedGradingMap D R 0 = ∑ i, (D i).comp (R i) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    by_cases hij : i.val ≤ j.val
    · have he : j.val - i.val ≠ 0 := by
        have hv : j.val ≠ i.val := Fin.val_ne_of_ne hji
        omega
      simp [hij, zero_pow he]
    · simp [hij]
  · simp

theorem analyticAt_dividedGradingMap (D : Fin N → F →L[ℝ] F)
    (R : Fin N → E →L[ℝ] F) (s : ℝ) :
    AnalyticAt ℝ (dividedGradingMap D R) s := by
  classical
  have hterm (i j : Fin N) : AnalyticAt ℝ
      (fun t : ℝ => if i.val ≤ j.val then
        t ^ (j.val-i.val) • (D i).comp (R j) else 0) s := by
    split_ifs
    · exact (analyticAt_id.pow _).smul analyticAt_const
    · exact analyticAt_const
  have hrow (i : Fin N) := Finset.analyticAt_sum Finset.univ (fun j _ => hterm i j)
  have h := Finset.analyticAt_sum Finset.univ (fun i _ => hrow i)
  convert h using 1
  ext t
  simp only [dividedGradingMap, Finset.sum_apply]
end Division

end Preiss
