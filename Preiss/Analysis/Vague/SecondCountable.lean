import Preiss.Analysis.Vague.Metrization
import Preiss.Analysis.CountableCoordinateTopology

/-! # A second-countable metric for vague convergence -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem exists_secondCountable_vagueMetrization (n : ℕ) :
    ∃ M : VagueMetrization n, letI := M.metric
      SecondCountableTopology (RegularEuclideanMeasure n) := by
  obtain ⟨F⟩ := exists_denseCompactTestFamily (X := Euclidean n)
  refine ⟨vagueMetrizationOfDenseCompactTests F, ?_⟩
  exact countableCoordinateMetric_secondCountable
    (fun j (μ : RegularEuclideanMeasure n) => ∫ x, F.tests j x ∂μ.val)
    (fun μ ν h => Subtype.ext (measure_eq_of_denseCompactTests F μ.val ν.val
      μ.property ν.property h))

end Preiss
