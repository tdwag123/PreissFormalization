module

public import Preiss.Rectifiability.EuclideanCarrier
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem rectifiable_iff_density_representation (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] :
    IsRectifiableMeasure m μ ↔ ∃ (S : Set (Euclidean n)) (f : Euclidean n → ℝ≥0∞),
      MeasurableSet S ∧ CountablyRectifiable m S ∧ SigmaFinite (((Measure.hausdorffMeasure (m : ℝ))).restrict S) ∧
      Measurable f ∧ μ = (((Measure.hausdorffMeasure (m : ℝ))).restrict S).withDensity f := by sorry

end Preiss
