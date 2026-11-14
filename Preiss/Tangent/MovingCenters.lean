import Preiss.Tangent.Continuity
import Preiss.Tangent.Algebra
import Preiss.Tangent.BlowupSupport
import Mathlib.Tactic.Abel

/-! # Moving centers with unchanged dimensional normalization -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem vague_dimensionalBlowup_moving_center
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (a : Euclidean n) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hlim : Measure.WeaklyConverges (fun i => dimensionalBlowup m μ a (r i)) ν)
    (a' : ℕ → Euclidean n) (y : Euclidean n)
    (hcenters : Tendsto (fun i => (r i)⁻¹ • (a' i - a)) atTop (𝓝 y)) :
    Measure.WeaklyConverges (fun i => dimensionalBlowup m μ (a' i) (r i))
      (dimensionalBlowup m ν y 1) := by
  have hconv := vague_dimensionalBlowup_moving (m := m)
    (fun i => dimensionalBlowup m μ a (r i)) ν
    (fun i => regular_dimensionalBlowup μ hμ a (hr i)) hν hlim
    (fun i => (r i)⁻¹ • (a' i - a)) y hcenters (fun _ => 1) 1
    (fun _ => zero_lt_one) zero_lt_one tendsto_const_nhds
  have heq (i : ℕ) : a + r i • ((r i)⁻¹ • (a' i - a)) = a' i := by
    rw [smul_smul, mul_inv_cancel₀ (hr i).ne', one_smul]
    abel
  simpa only [dimensionalBlowup_comp _ _ _ _ _ (hr _) zero_lt_one, heq, mul_one]
    using hconv

theorem dimensionalBlowup_one_ne_zero_of_mem_support (ν : Measure (Euclidean n))
    (y : Euclidean n) (hy : y ∈ ν.support) : dimensionalBlowup m ν y 1 ≠ 0 := by
  have hs : (0 : Euclidean n) ∈ (dimensionalBlowup m ν y 1).support := by
    rw [dimensionalBlowup_support ν y zero_lt_one]
    exact ⟨y, hy, by simp⟩
  intro hz
  simpa [hz] using hs

end Preiss
