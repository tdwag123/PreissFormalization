import Preiss.Density.Defs
import Preiss.Density.Limits
import FormalizingGMT.MarstrandTheorem

/-! # Density convention adapters

These interfaces connect the reusable definitions to the upstream conventions.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem density_iff_upstream (μ : Measure (Euclidean n)) (x : Euclidean n) :
    HasPositiveFiniteDensityAt m μ x ↔
      x ∈ positiveFiniteDensityExistsSet (m : ℝ) μ := by
  constructor
  · intro h
    refine ⟨h.hasDensity, ?_, ?_⟩
    · rw [density_eq_lower_of_hasDensity h.hasDensity]
      exact h.1
    · rw [density_eq_upper_of_hasDensity h.hasDensity]
      exact h.2.2
  · rintro ⟨hD, hpos, hfin⟩
    refine ⟨?_, lower_eq_upper_of_hasDensity hD, ?_⟩
    · rw [← density_eq_lower_of_hasDensity hD]
      exact hpos
    · rw [← density_eq_upper_of_hasDensity hD]
      exact hfin

theorem density_iff_openBall_limit (μ : Measure (Euclidean n)) (x : Euclidean n) :
    HasPositiveFiniteDensityAt m μ x ↔
      ∃ θ : ℝ≥0∞, 0 < θ ∧ θ < ∞ ∧
        Tendsto (fun r : ℝ ↦ μ (ball x r) / ENNReal.ofReal (r ^ m))
          (𝓝[>] 0) (𝓝 θ) := by
  sorry


end Preiss
