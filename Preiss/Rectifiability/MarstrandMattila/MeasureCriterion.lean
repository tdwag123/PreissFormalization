import Preiss.Rectifiability.MarstrandMattila.SetCriterion
import Preiss.Density.FinitePieces
import Preiss.Tangent.FlatApproximation
import Preiss.Tangent.DensityTransfer

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem ae_density_bounds_and_flat_tangents_restrict_hausdorff
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (S : Set (Euclidean n)) (hS : MeasurableSet S) (hfin : (Measure.hausdorffMeasure (m : ℝ)) S < ∞)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ENNReal.ofReal a • ((Measure.hausdorffMeasure (m : ℝ))).restrict S ≤ μ.restrict S)
    (hhi : μ.restrict S ≤ ENNReal.ofReal b • ((Measure.hausdorffMeasure (m : ℝ))).restrict S)
    (hd : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x)
    (ht : ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) :
    ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict S), HasPositiveFiniteDensitiesAt m (((Measure.hausdorffMeasure (m : ℝ))).restrict S) x ∧
      ∀ ν, IsTangentMeasure (((Measure.hausdorffMeasure (m : ℝ))).restrict S) ν x → IsFlat m ν := by sorry

theorem isRectifiableMeasure_of_ae_density_bounds_and_flat_tangents
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (hd : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x)
    (ht : ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) :
    IsRectifiableMeasure m μ := by sorry

end Preiss
