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
      ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r) := by
  obtain ⟨a, ha, R, hR, happ⟩ := h 1 zero_lt_one
  refine ⟨a, R, ha, hR, ?_⟩
  intro r hr hlt
  obtain ⟨V, _, hlower⟩ := happ r hr hlt
  simpa only [one_mul] using hlower x (by simp) (mem_ball_self hr)

end Preiss
