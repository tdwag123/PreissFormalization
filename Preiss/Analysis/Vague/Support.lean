import Preiss.Geometry.Euclidean
import FormalizingGMT.WeakConvergence.Basic

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace Preiss
variable {n : ℕ}

theorem exists_support_sequence_of_vague
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) (x : Euclidean n) (hx : x ∈ ν.support) :
    ∃ y : ℕ → Euclidean n, (∀ᶠ i in atTop, y i ∈ (μ i).support) ∧
      Tendsto y atTop (𝓝 x) := by
  sorry

theorem mem_support_of_vague_lower_ball_bound
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) (x : ℕ → Euclidean n) (y : Euclidean n)
    (hxy : Tendsto x atTop (𝓝 y)) (hx : ∀ i, x i ∈ (μ i).support)
    (hlower : ∀ r > 0, ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ᶠ i in atTop, c ≤ μ i (ball (x i) r)) : y ∈ ν.support := by
  sorry

end Preiss
