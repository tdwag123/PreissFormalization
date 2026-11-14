import Preiss.Uniform.Defs
import Preiss.Density.Defs
import FormalizingGMT.MarstrandTheorem

/-! # Adapters to FormalizingGMT uniform measures

The theorem bodies are explicit proof obligations.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem ae_tangent_uniform (hm : 0 < m) (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x →
      IsSUniform (m : ℝ) ν ∧ (0 : Euclidean n) ∈ ν.support := by
  sorry

/-- The pure unit ball law agrees with the upstream convention in positive dimension. -/
theorem isUnitUniform_iff (hm : 0 < m) (ν : Measure (Euclidean n)) :
    IsUnitUniform m ν ↔ IsSUniform (m : ℝ) ν ∧
      (0 : Euclidean n) ∈ ν.support ∧ ν (closedBall 0 1) = 1 := by
  sorry

end Preiss
