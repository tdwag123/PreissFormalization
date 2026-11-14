import Preiss.Rectifiability.GraphArea
import Preiss.Tangent.Restriction

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem ae_graph_hausdorff_blowup_limit (hm : 0 < m)
    (Γ : Set (Euclidean n)) (hΓ : IsLipschitzGraph m Γ) :
    ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict Γ), ∃ V : Plane m n, ∀ r : ℕ → ℝ,
      (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m (((Measure.hausdorffMeasure (m : ℝ))).restrict Γ) x (r i))
        (((Measure.hausdorffMeasure (m : ℝ))).restrict (V.1 : Set (Euclidean n))) := by sorry

end Preiss
