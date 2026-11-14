import Preiss.Density.HausdorffComparison
import FormalizingGMT.TangentMeasures.DensityIneqToTangentsLemmas2

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_finite_hausdorff_pieces_of_density_bounds
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x) :
    ∃ S : ℕ → Set (Euclidean n), (∀ j, MeasurableSet (S j)) ∧
      (∀ j, Bornology.IsBounded (S j)) ∧ (∀ j, (Measure.hausdorffMeasure (m : ℝ)) (S j) < ∞) ∧
      μ (⋃ j, S j)ᶜ = 0 ∧ ∀ j, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        ENNReal.ofReal a • ((Measure.hausdorffMeasure (m : ℝ))).restrict (S j) ≤ μ.restrict (S j) ∧
        μ.restrict (S j) ≤ ENNReal.ofReal b • ((Measure.hausdorffMeasure (m : ℝ))).restrict (S j) := by sorry

end Preiss
