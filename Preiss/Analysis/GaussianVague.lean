import Preiss.Analysis.GaussianGrowth
import FormalizingGMT.WeakConvergence.Basic

/-! # Gaussian polynomial tests under vague convergence

The legacy vague-convergence adapter is separated from the pure growth and
integrability API used by the Gaussian moment development.
-/

open MeasureTheory Filter
open scoped Topology
namespace Preiss
variable {n : ℕ}

theorem vague_integral_polynomial_mul_gaussian
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) (C p : ℝ)
    (hgrowth : ∀ i, HasPolynomialGrowthBound (μ i) C p)
    (hνgrowth : HasPolynomialGrowthBound ν C p)
    (P : MvPolynomial (Fin n) ℝ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun i => ∫ z, MvPolynomial.eval (fun j => z j) P *
      Real.exp (-s * ‖z‖ ^ 2) ∂μ i) atTop
      (𝓝 (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖ ^ 2) ∂ν)) := by
  sorry

end Preiss
