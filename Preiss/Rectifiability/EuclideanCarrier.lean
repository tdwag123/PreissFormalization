module

public import Preiss.Rectifiability.Basic
public import Preiss.Geometry.LipschitzExtension
public import Preiss.Geometry.PlaneMeasure
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_borel_sigmaFinite_carrier {s : Set (Euclidean n)}
    (hs : CountablyRectifiable m s) :
    ∃ T : Set (Euclidean n), MeasurableSet T ∧ CountablyRectifiable m T ∧
      (Measure.hausdorffMeasure (m : ℝ)) (s \ T) = 0 ∧ SigmaFinite (((Measure.hausdorffMeasure (m : ℝ))).restrict T) ∧
      ∃ K : ℕ → Set (Euclidean n), T = ⋃ i, K i ∧
        (∀ i, IsCompact (K i)) ∧ (∀ i, (Measure.hausdorffMeasure (m : ℝ)) (K i) < ∞) := by sorry

end Preiss
