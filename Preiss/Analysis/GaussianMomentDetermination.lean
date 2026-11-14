module
public import Preiss.Analysis.GaussianGrowth

@[expose] public section
open MeasureTheory
namespace Preiss
variable {n : ℕ}

theorem measure_eq_of_gaussian_polynomial_moments_eq
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (C p : ℝ) (hμgrowth : HasPolynomialGrowthBound μ C p)
    (hνgrowth : HasPolynomialGrowthBound ν C p)
    (heq : ∀ P : MvPolynomial (Fin n) ℝ,
      (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖ ^ 2) ∂μ) =
      ∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖ ^ 2) ∂ν) : μ = ν := by
  sorry

end Preiss
