module
public import Preiss.Analysis.BilinearTrace
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic
@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem bilinearTrace_eq_restrict_add_orthogonal
    (A : E →L[ℝ] E →L[ℝ] ℝ) (U : Submodule ℝ E) :
    bilinearTrace A = bilinearTrace (restrictBilinear A U) +
      bilinearTrace (restrictBilinear A Uᗮ) := by
  classical
  let e := stdOrthonormalBasis ℝ U
  let f := stdOrthonormalBasis ℝ Uᗮ
  let b := (e.prod f).map U.orthogonalDecomposition.symm
  rw [bilinearTrace_eq_sum_diagonal A b,
    bilinearTrace_eq_sum_diagonal _ e, bilinearTrace_eq_sum_diagonal _ f]
  simp only [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hbi : b (Sum.inl i) = (e i : E) := by simp [b]
    rw [hbi]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    have hbi : b (Sum.inr i) = (f i : E) := by simp [b]
    rw [hbi]
    rfl
end Preiss
