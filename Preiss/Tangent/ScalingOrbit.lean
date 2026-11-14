import Preiss.Tangent.Defs
import Preiss.Uniform.Defs

open MeasureTheory Filter
namespace Preiss
variable {n m : ℕ}

/-- Sequential closure of support-centered dimensional rescalings with radius at most one.
No small-radius limit is required, so this differs from a tangent measure at one point. -/
def IsUniformPseudotangent (m : ℕ) (ν ξ : Measure (Euclidean n)) : Prop :=
  ξ.Regular ∧ ∃ (a : ℕ → Euclidean n) (r : ℕ → ℝ),
    (∀ i, a i ∈ ν.support) ∧ (∀ i, 0 < r i ∧ r i ≤ 1) ∧
      Measure.WeaklyConverges (fun i => dimensionalBlowup m ν (a i) (r i)) ξ

theorem uniformPseudotangent_isUnitUniform (ν ξ : Measure (Euclidean n))
    (hν : IsUnitUniform m ν) (hξ : IsUniformPseudotangent m ν ξ) :
    IsUnitUniform m ξ := by
  sorry

theorem uniformPseudotangent_trans (ν ξ ζ : Measure (Euclidean n))
    (hν : IsUnitUniform m ν) (hξ : IsUniformPseudotangent m ν ξ)
    (hζ : IsUniformPseudotangent m ξ ζ) : IsUniformPseudotangent m ν ζ := by
  sorry

end Preiss
