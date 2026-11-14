import Preiss.Uniform.Defs
import Preiss.Tangent.Defs
import Preiss.Geometry.FlatMeasure

open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem flat_of_flat_at_infinity (μ ν : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (h∞ : IsTangentAtInfinity m μ ν) (hν : IsFlat m ν) : IsFlat m μ := by
  sorry

end Preiss
