import Preiss.Rectifiability.Decomposition
import Preiss.Rectifiability.MarstrandMattila.ProjectionNull
import Preiss.Rectifiability.MarstrandMattila.PackingContradiction
import Preiss.Rectifiability.MarstrandMattila.CompactSelection
import Preiss.Rectifiability.MarstrandMattila.HausdorffInputs

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem countablyRectifiable_of_ae_weaklyLinearlyApproximableAt
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    CountablyRectifiable m E := by sorry

end Preiss
