import Preiss.Density.Defs
import Preiss.Geometry.FlatMeasure
import FormalizingGMT.MarstrandTheorem

/-! # Part B of Preiss's argument: all tangents are flat -/
open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem all_tangents_flat_of_one (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x)
    (hu : ∀ ν, IsTangentMeasure μ ν x → IsSUniform (m : ℝ) ν)
    (hf : ∃ ν, IsTangentMeasure μ ν x ∧ IsFlat m ν) :
    ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν := by
  sorry

end Preiss
