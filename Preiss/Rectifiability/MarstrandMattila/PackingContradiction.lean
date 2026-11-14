import Preiss.Rectifiability.MarstrandMattila.Packing
import Preiss.Rectifiability.MarstrandMattila.CompactSelection

/-! # The Hausdorff-measure packing contradiction -/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem false_of_null_projections_and_uniform_weakApproximation
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hpos : 0 < (Measure.hausdorffMeasure (m : ℝ)) E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞)
    (hu : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), UpperPowerBoundAt m (((Measure.hausdorffMeasure (m : ℝ))).restrict E) x)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x)
    (hproj : ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' E) = 0) : False := by sorry


end Preiss
