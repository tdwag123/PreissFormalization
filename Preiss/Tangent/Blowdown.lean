import Preiss.Tangent.Compactness

open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem dimensionalTangent_of_tangentAtInfinity
    (μ ν ξ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hν : IsDimensionalTangent m μ ν x) (hξ : IsTangentAtInfinity m ν ξ) :
    IsDimensionalTangent m μ ξ x := by
  obtain ⟨hξreg, hξne, r, hr, _, hlim⟩ := hξ
  exact dimensionalTangent_closed μ x
    (fun i => dimensionalBlowup m ν 0 (r i)) ξ
    (fun i => dimensionalTangent_dilate μ ν x hν (r i) (hr i)) hlim hξreg hξne

end Preiss
