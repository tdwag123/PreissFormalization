module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! # Projection onto the span of a finite orthonormal family -/

open scoped BigOperators
namespace Preiss

theorem starProjection_span_orthonormal {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u : ι → E) (hu : Orthonormal ℝ u) :
    (Submodule.span ℝ (Set.range u)).starProjection =
      ∑ i, InnerProductSpace.rankOne ℝ (u i) (u i) := by
  have hb : Orthonormal ℝ (Module.Basis.span hu.linearIndependent) := by
    have heq : (Module.Basis.span hu.linearIndependent : ι → Submodule.span ℝ (Set.range u)) =
        fun i => ⟨u i, Submodule.subset_span (Set.mem_range_self i)⟩ := by
      funext i
      exact Module.Basis.span_apply hu.linearIndependent i
    rw [heq]
    exact orthonormal_span hu
  let b := (Module.Basis.span hu.linearIndependent).toOrthonormalBasis hb
  have hcoe (i : ι) : (b i : E) = u i := by
    simp [b, Module.Basis.coe_toOrthonormalBasis, Module.Basis.span_apply]
  simpa only [hcoe] using b.starProjection_eq_sum_rankOne

theorem starProjection_span_orthonormal_apply {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u : ι → E) (hu : Orthonormal ℝ u) (x : E) :
    (Submodule.span ℝ (Set.range u)).starProjection x =
      ∑ i, (inner ℝ (u i) x) • u i := by
  rw [starProjection_span_orthonormal u hu]
  simp

end Preiss
