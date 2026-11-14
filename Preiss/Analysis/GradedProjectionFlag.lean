module
public import Preiss.Analysis.Grading
public import Preiss.Analysis.GradedDivision
public import Mathlib.Analysis.Normed.Operator.Banach
public import Preiss.Analysis.NestedProjections
public import Mathlib.Tactic

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def kernelGradingFlag {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (i : ℕ) : Submodule ℝ V where
  carrier := {x | ∀ j : Fin N, j.val < i → P j (x : E) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j hj
    simp only [Submodule.coe_add, map_add, hx j hj, hy j hj, add_zero]
  smul_mem' := by
    intro c x hx j hj
    simp only [Submodule.coe_smul, map_smul, hx j hj, smul_zero]

theorem mem_kernelGradingFlag {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (i : ℕ) (x : V) :
    x ∈ kernelGradingFlag P V i ↔ ∀ j : Fin N, j.val < i → P j (x : E) = 0 := Iff.rfl

theorem kernelGradingFlag_antitone {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) : Antitone (kernelGradingFlag P V) := by
  intro i j hij x hx k hk
  exact hx k (lt_of_lt_of_le hk hij)

theorem kernelGradingFlag_zero {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) : kernelGradingFlag P V 0 = ⊤ := by
  ext x
  simp [mem_kernelGradingFlag]

theorem kernelGradingFlag_end {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) : kernelGradingFlag P V N = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hz := congrArg (fun T : E →L[ℝ] E => T (x : E)) hP.2.2.2
  have hzero (i : Fin N) : P i (x : E) = 0 := hx i i.isLt
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.id_apply,
    hzero, Finset.sum_const_zero] at hz
  exact Subtype.ext hz.symm

noncomputable def flagProjectionLayer {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (i : Fin N) : V →L[ℝ] V :=
  nestedProjectionLayer (kernelGradingFlag P V) i.val

theorem flagProjectionLayer_isOrthogonalGrading {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) :
    IsOrthogonalGrading (flagProjectionLayer P V) := by
  refine ⟨fun i => nestedProjectionLayer_symmetric _ _,
    fun i => nestedProjectionLayer_idempotent _ (kernelGradingFlag_antitone P V) _,
    fun i j hij => nestedProjectionLayer_comp_eq_zero _
      (kernelGradingFlag_antitone P V) (Fin.val_ne_of_ne hij), ?_⟩
  change (∑ i : Fin N, nestedProjectionLayer (kernelGradingFlag P V) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (nestedProjectionLayer (kernelGradingFlag P V)) N,
    sum_nestedProjectionLayer, kernelGradingFlag_zero,
    kernelGradingFlag_end P hP V, Submodule.starProjection_top, Submodule.starProjection_bot,
    sub_zero]

noncomputable def compressedGradingPiece {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (i : Fin N) : V →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp ((P i).comp V.subtypeL)

theorem flagProjectionLayer_compressed_inner {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) (i : Fin N) (x : V)
    (hx : x ∈ kernelGradingFlag P V i.val) :
    inner ℝ (flagProjectionLayer P V i (compressedGradingPiece P V i x)) x =
      ‖P i (x : E)‖ ^ 2 := by
  have hdiff := sub_nestedProjectionLayer_mem (kernelGradingFlag P V) i.val hx
  have hz : P i ((x - flagProjectionLayer P V i x : V) : E) = 0 :=
    hdiff i (Nat.lt_succ_self i.val)
  have hpi : P i ((flagProjectionLayer P V i x : V) : E) = P i (x : E) := by
    exact (sub_eq_zero.mp (by simpa only [Submodule.coe_sub, map_sub] using hz)).symm
  rw [flagProjectionLayer, nestedProjectionLayer_symmetric]
  change inner ℝ (V.orthogonalProjectionOnto (P i (x : E)))
    (flagProjectionLayer P V i x) = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  have hidem : P i (P i (x : E)) = P i (x : E) :=
    congrArg (fun T : E →L[ℝ] E => T (x : E)) (hP.2.1 i)
  calc
    _ = inner ℝ (P i (P i (x : E))) ((flagProjectionLayer P V i x : V) : E) := by rw [hidem]
    _ = inner ℝ (P i (x : E)) (P i ((flagProjectionLayer P V i x : V) : E)) := hP.1 _ _ _
    _ = _ := by rw [hpi, real_inner_self_eq_norm_sq]

noncomputable def dividedGradingConstant {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) : V →L[ℝ] V :=
  ∑ i, (flagProjectionLayer P V i).comp (compressedGradingPiece P V i)

theorem flagProjectionLayer_dividedGradingConstant {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) (i : Fin N) (x : V) :
    flagProjectionLayer P V i (dividedGradingConstant P V x) =
      flagProjectionLayer P V i (compressedGradingPiece P V i x) := by
  classical
  have hD := flagProjectionLayer_isOrthogonalGrading P hP V
  simp only [dividedGradingConstant, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single i]
  · exact congrArg (fun T : V →L[ℝ] V => T (compressedGradingPiece P V i x)) (hD.2.1 i)
  · intro j _ hji
    exact congrArg (fun T : V →L[ℝ] V => T (compressedGradingPiece P V j x))
      (hD.2.2.1 i j (Ne.symm hji))
  · simp

theorem dividedGradingConstant_injective {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) :
    Function.Injective (dividedGradingConstant P V) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hflag : ∀ i : ℕ, i ≤ N → x ∈ kernelGradingFlag P V i := by
    intro i
    induction i with
    | zero => intro _; rw [kernelGradingFlag_zero]; trivial
    | succ i ih =>
      intro hi
      have hxi := ih (by omega)
      let j : Fin N := ⟨i, by omega⟩
      have hz : flagProjectionLayer P V j (compressedGradingPiece P V j x) = 0 := by
        rw [← flagProjectionLayer_dividedGradingConstant P hP V j x, hx, map_zero]
      have hnorm := flagProjectionLayer_compressed_inner P hP V j x hxi
      rw [hz, inner_zero_left] at hnorm
      have hpj : P j (x : E) = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (P j (x : E))])
      intro k hk
      by_cases hki : k.val < i
      · exact hxi k hki
      · have hkj : k = j := Fin.ext (by dsimp [j]; omega)
        simpa only [hkj] using hpj
  have hbottom := hflag N le_rfl
  rw [kernelGradingFlag_end P hP V] at hbottom
  exact hbottom


noncomputable def projectedGradingPiece {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (i : Fin N) : E →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp (P i)

theorem flagProjectionLayer_projectedGradingPiece_eq_zero {N : ℕ}
    (P : Fin N → E →L[ℝ] E) (hP : IsOrthogonalGrading P) (V : Submodule ℝ E)
    (i j : Fin N) (hji : j.val < i.val) :
    (flagProjectionLayer P V i).comp (projectedGradingPiece P V j) = 0 := by
  ext x
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change inner ℝ (flagProjectionLayer P V i (projectedGradingPiece P V j x))
    (flagProjectionLayer P V i (projectedGradingPiece P V j x)) = 0
  rw [flagProjectionLayer, nestedProjectionLayer_symmetric]
  change inner ℝ (V.orthogonalProjectionOnto (P j x))
    (flagProjectionLayer P V i (flagProjectionLayer P V i (projectedGradingPiece P V j x))) = 0
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, hP.1]
  have hmem := nestedProjectionLayer_mem (kernelGradingFlag P V)
    (kernelGradingFlag_antitone P V) i.val
    (flagProjectionLayer P V i (projectedGradingPiece P V j x))
  have hz : P j ((flagProjectionLayer P V i (flagProjectionLayer P V i
      (projectedGradingPiece P V j x)) : V) : E) = 0 := hmem j hji
  rw [hz, inner_zero_right]

noncomputable def dividedFlagMap {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (s : ℝ) : E →L[ℝ] V :=
  dividedGradingMap (flagProjectionLayer P V) (projectedGradingPiece P V) s

noncomputable def dividedFlagOperator {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (s : ℝ) : V →L[ℝ] V :=
  (dividedFlagMap P V s).comp V.subtypeL

theorem dividedFlagOperator_zero {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) : dividedFlagOperator P V 0 = dividedGradingConstant P V := by
  ext x
  simp only [dividedFlagOperator, dividedFlagMap, dividedGradingMap_zero,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, dividedGradingConstant]
  rfl

theorem weightedGrading_comp_dividedFlagMap {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) (s : ℝ) :
    (weightedGrading (flagProjectionLayer P V) s).comp (dividedFlagMap P V s) =
      V.orthogonalProjectionOnto.comp (weightedGrading P s) := by
  rw [dividedFlagMap, weightedGrading_comp_dividedGradingMap _
    (flagProjectionLayer_isOrthogonalGrading P hP V) _
    (flagProjectionLayer_projectedGradingPiece_eq_zero P hP V)]
  ext x
  simp only [weightedGrading, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_smul, projectedGradingPiece]

theorem analyticAt_dividedFlagMap {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (s : ℝ) : AnalyticAt ℝ (dividedFlagMap P V) s :=
  analyticAt_dividedGradingMap _ _ _

theorem analyticAt_dividedFlagOperator {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (V : Submodule ℝ E) (s : ℝ) : AnalyticAt ℝ (dividedFlagOperator P V) s := by
  exact ((ContinuousLinearMap.compL ℝ V E V).analyticAt_bilinear _).comp₂
    (analyticAt_dividedFlagMap P V s) analyticAt_const

theorem isUnit_dividedFlagOperator_zero {N : ℕ} (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) :
    IsUnit (dividedFlagOperator P V 0) := by
  rw [dividedFlagOperator_zero, ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨dividedGradingConstant_injective P hP V,
    LinearMap.surjective_of_injective (f := (dividedGradingConstant P V).toLinearMap)
      (dividedGradingConstant_injective P hP V)⟩

end Preiss
