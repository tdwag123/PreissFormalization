import Preiss.Rectifiability.Cones
import Preiss.Density.Defs

/-! # An approximate cone criterion for rectifiability

This companion criterion records De Lellis Proposition 4.6. It is independent
of the Marstrand--Mattila packing route used by the main Preiss proof.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- Positive lower density and concentration in one finite-aperture cone suffice. -/
theorem countablyRectifiable_of_ae_cone_approximation
    (E : Set (Euclidean n)) (hE : MeasurableSet E)
    (hfin : (Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean n)) E < ∞)
    (h : ∀ᵐ x ∂(Measure.hausdorffMeasure (m : ℝ)).restrict E,
      0 < dimensional_lower_density
        ((Measure.hausdorffMeasure (m : ℝ)).restrict E).toOuterMeasure (m : ℝ) x ∧
      ∃ (V : Plane m n) (a : ℝ), 0 ≤ a ∧
        Tendsto (fun r : ℝ =>
          (Measure.hausdorffMeasure (m : ℝ)) ((E ∩ ball x r) \ cone x V a) /
            ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0)) :
    CountablyRectifiable m E := by
  sorry

end Preiss
