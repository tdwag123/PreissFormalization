module
public import Preiss.Uniform.MomentForms
public import Preiss.Uniform.Defs
public import Preiss.Analysis.GaussianGrowth
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Preiss
variable {n m : ℕ}

theorem IsUnitUniform.hasPolynomialGrowthBound (μ : Measure (Euclidean n))
    (hμ : IsUnitUniform m μ) : HasPolynomialGrowthBound μ 1 (m : ℝ) := by
  refine ⟨by positivity, by positivity, ?_⟩
  intro R hR
  rw [hμ.2.2 0 hμ.2.1 R hR]
  apply ENNReal.ofReal_le_ofReal
  rw [one_mul, Real.rpow_natCast]
  exact pow_le_pow_left₀ hR.le (by linarith) m

theorem integrable_gaussianMomentKernel_of_integrable_norm
    (μ : Measure (Euclidean n)) (k : ℕ) (s : ℝ)
    (hint : Integrable (fun z => ‖z‖ ^ k * Real.exp (-s * ‖z‖ ^ 2)) μ) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z) μ := by
  apply hint.mono'
  · exact (Continuous.smul (by fun_prop) (continuous_momentKernel k)).aestronglyMeasurable
  · filter_upwards [] with z
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left (norm_momentKernel_le k z)
      (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem integrable_gaussianMomentKernel (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z) μ := by
  exact integrable_gaussianMomentKernel_of_integrable_norm μ k s
    (integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ.1 1 (m : ℝ)
      (IsUnitUniform.hasPolynomialGrowthBound μ hμ) k s hs)

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
