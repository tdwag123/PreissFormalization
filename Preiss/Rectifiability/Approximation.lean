import Preiss.Tangent.Defs

open MeasureTheory Metric Set
open scoped ENNReal

namespace Preiss
variable {n : ℕ}

/-- De Lellis 5.4, with mathlib's Hausdorff normalization. Constants absorb
the fixed conversion factor to normalized Hausdorff measure. -/
def WeaklyLinearlyApproximableAt (m : ℕ) (s : Set (Euclidean n))
    (x : Euclidean n) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r < r₀ → ∃ V : Plane m n,
      (Measure.hausdorffMeasure (m : ℝ))
        ((s ∩ ball x r) \ {z | infDist (z - x) (V.1 : Set (Euclidean n)) ≤ η * r})
          < ENNReal.ofReal (η * r ^ m) ∧
      ∀ z : Euclidean n, z - x ∈ V.1 → z ∈ ball x r →
        ENNReal.ofReal (a * r ^ m) ≤
          (Measure.hausdorffMeasure (m : ℝ)) (s ∩ ball z (η * r))

end Preiss
