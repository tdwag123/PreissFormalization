module
public import Preiss.Tangent.Blowup
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace Preiss
variable {n m : ℕ}

theorem dimensionalBlowup_comp (μ : Measure (Euclidean n)) (a b : Euclidean n)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    dimensionalBlowup m (dimensionalBlowup m μ a r) b s =
      dimensionalBlowup m μ (a + r • b) (r * s) := by
  sorry

theorem dimensionalBlowup_smul (μ : Measure (Euclidean n)) (a : Euclidean n)
    (r : ℝ) (hr : 0 < r) (c : ℝ≥0∞) :
    dimensionalBlowup m (c • μ) a r = c • dimensionalBlowup m μ a r := by
  sorry

theorem dimensionalBlowup_map_linearIsometry {k : ℕ}
    (L : Euclidean n →ₗᵢ[ℝ] Euclidean k) (μ : Measure (Euclidean n))
    (a : Euclidean n) (r : ℝ) (hr : 0 < r) :
    dimensionalBlowup m (μ.map L) (L a) r = (dimensionalBlowup m μ a r).map L := by
  sorry

end Preiss
