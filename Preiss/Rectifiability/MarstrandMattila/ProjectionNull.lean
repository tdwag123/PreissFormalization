module

public import Preiss.Rectifiability.PurelyUnrectifiable
public import Preiss.Rectifiability.Cones
public import Preiss.Rectifiability.ProjectionEstimate
public import Preiss.Rectifiability.WeakApproximation.Uniformization
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem ae_exists_outside_cone_of_purelyUnrectifiable
    (C : Set (Euclidean n)) (hp : PurelyUnrectifiable m C)
    (V : Plane m n) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᵐ a ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict C), ∀ r : ℝ, 0 < r →
      ∃ b ∈ C ∩ ball a r, b ∉ cone a V A := by sorry

theorem measure_projection_eq_zero_of_purelyUnrectifiable_weakApproximation
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) (hp : PurelyUnrectifiable m E)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' E) = 0 := by sorry

end Preiss
