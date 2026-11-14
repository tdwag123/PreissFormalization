module
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.Trace

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def bilinearTrace (A : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  LinearMap.trace ℝ E (InnerProductSpace.continuousLinearMapOfBilin A).toLinearMap

noncomputable def restrictBilinear (A : E →L[ℝ] E →L[ℝ] ℝ) (V : Submodule ℝ E) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V E ℝ).flip V.subtypeL).comp (A.comp V.subtypeL)

theorem bilinearTrace_eq_sum_diagonal {ι : Type*} [Fintype ι]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (e : OrthonormalBasis ι ℝ E) :
    bilinearTrace A = ∑ i, A (e i) (e i) := by
  sorry

end Preiss
