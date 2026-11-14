module
public import Preiss.Analysis.BilinearTrace
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_integral_inner_pow_even (y : E) (j : ℕ) :
    (∫ v, (inner ℝ y v) ^ (2 * j) ∂stdGaussian E) =
      ((2 * j).factorial : ℝ) / (2 ^ j * (j.factorial : ℝ)) * ‖y‖ ^ (2 * j) := by
  sorry

theorem gaussian_integral_inner_sq_mul_inner_sq (y z : E) :
    (∫ v, (inner ℝ y v) ^ 2 * (inner ℝ z v) ^ 2 ∂stdGaussian E) =
      ‖y‖ ^ 2 * ‖z‖ ^ 2 + 2 * (inner ℝ y z) ^ 2 := by
  sorry

theorem gaussian_integral_bilinear_eq_trace (A : E →L[ℝ] E →L[ℝ] ℝ) :
    (∫ v, A v v ∂stdGaussian E) = bilinearTrace A := by
  sorry

theorem gaussian_integral_bilinear_sq_ge_trace_sq
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ u v, A u v = A v u)
    (hdim : 0 < Module.finrank ℝ E) :
    (1 + 2 / (Module.finrank ℝ E : ℝ)) * (bilinearTrace A) ^ 2 ≤
      ∫ v, (A v v) ^ 2 ∂stdGaussian E := by
  sorry

theorem gaussian_integral_bilinear_sq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ u v, A u v = A v u) :
    (∫ v, (A v v) ^ 2 ∂stdGaussian E) =
      (bilinearTrace A) ^ 2 + 2 * ∑ i, ∑ j, (A (e i) (e j)) ^ 2 := by
  sorry

end Preiss
