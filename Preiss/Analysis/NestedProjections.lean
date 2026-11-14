module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic.Abel

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem starProjection_comp_of_ge {U V : Submodule ℝ E} (h : U ≤ V) :
    V.starProjection.comp U.starProjection = U.starProjection := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (h (U.starProjection_apply_mem x))

noncomputable def nestedProjectionLayer (U : ℕ → Submodule ℝ E) (i : ℕ) : E →L[ℝ] E :=
  (U i).starProjection - (U (i+1)).starProjection

theorem nestedProjectionLayer_symmetric (U : ℕ → Submodule ℝ E) (i : ℕ) (x y : E) :
    inner ℝ (nestedProjectionLayer U i x) y = inner ℝ x (nestedProjectionLayer U i y) := by
  simp only [nestedProjectionLayer, ContinuousLinearMap.sub_apply, inner_sub_left,
    inner_sub_right, Submodule.inner_starProjection_left_eq_right]

theorem nestedProjectionLayer_mem (U : ℕ → Submodule ℝ E) (hU : Antitone U)
    (i : ℕ) (x : E) : nestedProjectionLayer U i x ∈ U i := by
  exact (U i).sub_mem ((U i).starProjection_apply_mem x)
    (hU (Nat.le_succ i) ((U (i+1)).starProjection_apply_mem x))

theorem nestedProjectionLayer_eq_zero_of_mem (U : ℕ → Submodule ℝ E) (hU : Antitone U)
    (i : ℕ) {x : E} (hx : x ∈ U (i+1)) : nestedProjectionLayer U i x = 0 := by
  simp only [nestedProjectionLayer, ContinuousLinearMap.sub_apply,
    Submodule.starProjection_eq_self_iff.mpr hx,
    Submodule.starProjection_eq_self_iff.mpr (hU (Nat.le_succ i) hx), sub_self]

theorem sub_nestedProjectionLayer_mem (U : ℕ → Submodule ℝ E) (i : ℕ)
    {x : E} (hx : x ∈ U i) : x - nestedProjectionLayer U i x ∈ U (i+1) := by
  simp only [nestedProjectionLayer, ContinuousLinearMap.sub_apply,
    Submodule.starProjection_eq_self_iff.mpr hx, sub_sub_cancel]
  exact (U (i+1)).starProjection_apply_mem x

theorem nestedProjectionLayer_idempotent (U : ℕ → Submodule ℝ E) (hU : Antitone U)
    (i : ℕ) : (nestedProjectionLayer U i).comp (nestedProjectionLayer U i) =
      nestedProjectionLayer U i := by
  have hsmall := Submodule.starProjection_comp_starProjection_of_le (hU (Nat.le_succ i))
  have hlarge := starProjection_comp_of_ge (hU (Nat.le_succ i))
  have hsmall' (x : E) : (U (i+1)).starProjection ((U i).starProjection x) =
      (U (i+1)).starProjection x := congrArg (fun T : E →L[ℝ] E => T x) hsmall
  have hlarge' (x : E) : (U i).starProjection ((U (i+1)).starProjection x) =
      (U (i+1)).starProjection x := congrArg (fun T : E →L[ℝ] E => T x) hlarge
  ext x
  simp only [nestedProjectionLayer, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub, hsmall', hlarge',
    Submodule.starProjection_eq_self_iff.mpr ((U i).starProjection_apply_mem x),
    Submodule.starProjection_eq_self_iff.mpr ((U (i+1)).starProjection_apply_mem x)]
  abel

theorem nestedProjectionLayer_comp_eq_zero (U : ℕ → Submodule ℝ E) (hU : Antitone U)
    {i j : ℕ} (hij : i ≠ j) :
    (nestedProjectionLayer U i).comp (nestedProjectionLayer U j) = 0 := by
  have hlt {a b : ℕ} (hab : a < b) :
      (nestedProjectionLayer U a).comp (nestedProjectionLayer U b) = 0 := by
    ext x
    apply nestedProjectionLayer_eq_zero_of_mem U hU a
    exact hU (Nat.succ_le_of_lt hab) (nestedProjectionLayer_mem U hU b x)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hlt hij
  · ext x
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hz (z : E) : nestedProjectionLayer U j (nestedProjectionLayer U i z) = 0 :=
      congrArg (fun T : E →L[ℝ] E => T z) (hlt hji)
    change inner ℝ (nestedProjectionLayer U i (nestedProjectionLayer U j x))
      (nestedProjectionLayer U i (nestedProjectionLayer U j x)) = 0
    rw [nestedProjectionLayer_symmetric,
      nestedProjectionLayer_symmetric U j, hz, inner_zero_right]

theorem sum_nestedProjectionLayer (U : ℕ → Submodule ℝ E) (N : ℕ) :
    ∑ i ∈ Finset.range N, nestedProjectionLayer U i =
      (U 0).starProjection - (U N).starProjection := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, nestedProjectionLayer]
    abel
end Preiss
