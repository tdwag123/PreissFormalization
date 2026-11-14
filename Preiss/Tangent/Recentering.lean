import Preiss.Tangent.Defs
import Preiss.Density.Defs
import Mathlib.MeasureTheory.Measure.Support

/-! # Simultaneous recentering of dimensional tangents

The outer almost-everywhere quantifier gives one null exceptional set for all tangent
measures, all points of their supports, and all positive radii. The proof obligation uses
measurable hulls of arbitrary bad-center sets rather than assuming these sets measurable.
-/

open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem ae_recenter_dimensionalTangent (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (hm : 0 < m) (hmn : m ≤ n)
    (hdens : ∀ᵐ a ∂μ, HasPositiveFiniteDensityAt m μ a) :
    ∀ᵐ a ∂μ, ∀ ν : Measure (Euclidean n), IsDimensionalTangent m μ ν a →
      ∀ y ∈ ν.support, ∀ r : ℝ, 0 < r →
        IsDimensionalTangent m μ (dimensionalBlowup m ν y r) a := by
  sorry

end Preiss
