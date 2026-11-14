module

public import Preiss.Rectifiability.WeakApproximation.Defs

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem lower_power_bound_of_weakApproximation (μ : Measure (Euclidean n)) (x : Euclidean n)
    (h : MeasureWeaklyLinearlyApproximableAt m μ x) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r) := by sorry

end Preiss
