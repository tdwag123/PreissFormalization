module
public import Preiss.Geometry.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section
open MeasureTheory Metric Set Filter
open scoped Topology
namespace Preiss
variable {n : ℕ}

def HasPolynomialGrowthBound (μ : Measure (Euclidean n)) (C p : ℝ) : Prop :=
  0 ≤ C ∧ 0 ≤ p ∧ ∀ R > 0,
    μ (closedBall 0 R) ≤ ENNReal.ofReal (C * (1 + R) ^ p)

theorem integrable_norm_pow_mul_gaussian_of_polynomial_growth
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (C p : ℝ)
    (hgrowth : HasPolynomialGrowthBound μ C p) (d : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2)) μ := by
  sorry

theorem gaussian_polynomial_uniform_tail (C p : ℝ) (d : ℕ) (s : ℝ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ (μ : Measure (Euclidean n)), μ.Regular →
      HasPolynomialGrowthBound μ C p → ∀ R ≥ R₀,
      (∫ z in (closedBall 0 R)ᶜ, ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2) ∂μ) < ε := by
  sorry

theorem hasDerivAt_integral_polynomial_mul_gaussian
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (C p : ℝ)
    (hgrowth : HasPolynomialGrowthBound μ C p)
    (P : MvPolynomial (Fin n) ℝ) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => ∫ z, MvPolynomial.eval (fun j => z j) P *
      Real.exp (-t * ‖z‖ ^ 2) ∂μ)
      (-(∫ z, ‖z‖ ^ 2 * MvPolynomial.eval (fun j => z j) P *
        Real.exp (-s * ‖z‖ ^ 2) ∂μ)) s := by
  sorry

end Preiss
