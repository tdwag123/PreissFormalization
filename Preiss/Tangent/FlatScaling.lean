module
public import Preiss.Tangent.Blowup
public import Preiss.Geometry.FlatMeasure

@[expose] public section
open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem isFlat_dimensionalBlowup (μ : Measure (Euclidean n)) (hμ : IsFlat m μ)
    (x : Euclidean n) (hx : x ∈ μ.support) (r : ℝ) (hr : 0 < r) :
    IsFlat m (dimensionalBlowup m μ x r) := by
  sorry

theorem isFlat_of_dimensionalBlowup_zero (μ : Measure (Euclidean n))
    (r : ℝ) (hr : 0 < r) (h : IsFlat m (dimensionalBlowup m μ 0 r)) :
    IsFlat m μ := by
  sorry

theorem isFlat_map_linearIsometry {k : ℕ}
    (L : Euclidean n →ₗᵢ[ℝ] Euclidean k) (μ : Measure (Euclidean n))
    (hμ : IsFlat m μ) : IsFlat m (μ.map L) := by
  sorry

end Preiss
