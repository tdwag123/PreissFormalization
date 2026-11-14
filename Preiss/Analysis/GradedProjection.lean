module
public import Preiss.Analysis.Grading
public import Mathlib.Analysis.Analytic.Basic

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}

theorem analyticAt_weightedProjection_zero (P : Fin N → E →L[ℝ] E)
    (hP : IsOrthogonalGrading P) (V : Submodule ℝ E) :
    ∃ Q : ℝ → E →L[ℝ] E, AnalyticAt ℝ Q 0 ∧
      ∀ s : ℝ, 0 < s → IsCompl V (weightedComplement P V s) ∧
        (∀ x, Q s x ∈ V) ∧ (∀ v ∈ V, Q s v = v) ∧
        (∀ w ∈ weightedComplement P V s, Q s w = 0) := by
  sorry

end Preiss
