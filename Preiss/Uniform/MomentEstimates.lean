module
public import Preiss.Uniform.MomentForms
public import Preiss.Uniform.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Preiss
variable {n m : ℕ}

theorem integrable_gaussianMomentKernel (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z) μ := by
  sorry

theorem norm_gaussianMomentForm_le (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (Euclidean n)), IsUnitUniform m μ →
      ∀ k : ℕ, 0 < k → ∀ s : ℝ, 0 < s →
      ‖gaussianMomentForm μ k s‖ ≤ C * 2 ^ k * (k : ℝ) ^ ((k : ℝ) / 2) *
        s ^ ((k : ℝ) / 2) / (k.factorial : ℝ) := by
  sorry

theorem hasSum_gaussianMoment_diagonal (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (x : Euclidean n) (hx : x ∈ μ.support)
    (s : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℕ => gaussianMomentForm μ k s (fun _ => x))
      (Real.exp (s * ‖x‖ ^ 2)) ∧
    Summable (fun k : ℕ => |gaussianMomentForm μ k s (fun _ => x)|) := by
  sorry

theorem gaussianMoment_taylor_remainder (hm : 0 < m) (q : ℕ) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (Euclidean n)), IsUnitUniform m μ →
      ∀ x ∈ μ.support, ∀ s : ℝ, 0 < s →
      |(∑ k ∈ Finset.range (2 * q), gaussianMomentForm μ (k + 1) s (fun _ => x)) -
        ∑ j ∈ Finset.range q, s ^ (j + 1) * ‖x‖ ^ (2 * (j + 1)) /
          ((j + 1).factorial : ℝ)| ≤ C * (s * ‖x‖ ^ 2) ^ ((q : ℝ) + 1 / 2) := by
  sorry

end Preiss
