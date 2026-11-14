module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Analytic.Basic

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}

def IsOrthogonalGrading (P : Fin N → E →L[ℝ] E) : Prop :=
  (∀ i x y, inner ℝ (P i x) y = inner ℝ x (P i y)) ∧
  (∀ i, (P i).comp (P i) = P i) ∧
  (∀ i j, i ≠ j → (P i).comp (P j) = 0) ∧
  (∑ i, P i) = ContinuousLinearMap.id ℝ E

noncomputable def weightedGrading (P : Fin N → E →L[ℝ] E) (s : ℝ) : E →L[ℝ] E :=
  ∑ i, (s ^ (i.val + 1)) • P i

def weightedComplement (P : Fin N → E →L[ℝ] E) (V : Submodule ℝ E) (s : ℝ) :
    Submodule ℝ E := Vᗮ.comap (weightedGrading P s).toLinearMap

theorem analyticAt_weightedProjection_zero (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) :
    ∃ Q : ℝ → E →L[ℝ] E, AnalyticAt ℝ Q 0 ∧
      ∀ s : ℝ, 0 < s → IsCompl V (weightedComplement P V s) ∧
        (∀ x, Q s x ∈ V) ∧ (∀ v ∈ V, Q s v = v) ∧
        (∀ w ∈ weightedComplement P V s, Q s w = 0) := by
  sorry

end Preiss
