import Preiss.Density.Defs
import FormalizingGMT.MarstrandTheorem

/-! # Density convention adapters

The theorem bodies are explicit proof obligations.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem density_iff_upstream (μ : Measure (Euclidean n)) (x : Euclidean n) :
    HasPositiveFiniteDensityAt m μ x ↔
      x ∈ positiveFiniteDensityExistsSet (m : ℝ) μ := by
  sorry

theorem density_iff_openBall_limit (μ : Measure (Euclidean n)) (x : Euclidean n) :
    HasPositiveFiniteDensityAt m μ x ↔
      ∃ θ : ℝ≥0∞, 0 < θ ∧ θ < ∞ ∧
        Tendsto (fun r : ℝ ↦ μ (ball x r) / ENNReal.ofReal (r ^ m))
          (𝓝[>] 0) (𝓝 θ) := by
  sorry


end Preiss
