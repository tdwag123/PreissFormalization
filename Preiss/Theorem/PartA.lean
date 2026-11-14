import Preiss.Density.Defs
import Preiss.Geometry.FlatMeasure
import FormalizingGMT.TangentMeasures.Basic

/-! # Part A of Preiss's argument: a flat tangent almost everywhere -/
open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem ae_exists_flat_tangent (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    ∀ᵐ x ∂μ, ∃ ν, IsTangentMeasure μ ν x ∧ IsFlat m ν := by
  sorry

end Preiss
