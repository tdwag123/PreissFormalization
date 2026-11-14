import Preiss.Density.Defs
import FormalizingGMT.TangentMeasures.Basic

/-! # Existence of nonzero tangent measures

The theorem bodies are explicit proof obligations.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem tangent_exists (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) (h : HasPositiveFiniteDensitiesAt m μ x) :
    ∃ ν, IsTangentMeasure μ ν x := by
  sorry


end Preiss
