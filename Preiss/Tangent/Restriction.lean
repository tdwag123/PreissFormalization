import Preiss.Tangent.Defs
import FormalizingGMT.TangentMeasures.MatchingTangents
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Reuse GMT restriction and density matching, including fixed-test perturbation estimates. -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {n : ℕ}

/-- A finite measure absolutely continuous with respect to a locally finite Euclidean
measure has the same full tangent cone at almost every point for the smaller measure. -/
theorem ae_isTangentMeasure_iff_of_absolutelyContinuous
    (μ ν : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hνμ : ν ≪ μ) :
    ∀ᵐ x ∂ν, ∀ ξ, IsTangentMeasure μ ξ x ↔ IsTangentMeasure ν ξ x := by
  let φ : Euclidean n → ℝ := fun x ↦ (ν.rnDeriv μ x).toReal
  have hφint : Integrable φ μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (ν := μ) (measure_ne_top ν univ))
  apply isTangentMeasure_iff_ae_of_density μ ν inferInstance inferInstance φ
    (fun x ↦ ENNReal.toReal_nonneg) hφint.locallyIntegrable
  intro B hB
  dsimp only [φ]
  rw [Measure.setIntegral_toReal_rnDeriv' hνμ hB]
  exact (ENNReal.ofReal_toReal (measure_ne_top ν B)).symm

end Preiss
