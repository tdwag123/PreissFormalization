import Preiss.Tangent.Defs

open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem dimensionalTangent_of_tangentAtInfinity
    (μ ν ξ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hν : IsDimensionalTangent m μ ν x) (hξ : IsTangentAtInfinity m ν ξ) :
    IsDimensionalTangent m μ ξ x := by
  sorry

end Preiss
