import Preiss.Uniform.MomentCoefficients
import Preiss.Uniform.Defs
import Mathlib.Algebra.MvPolynomial.Eval

open MeasureTheory Filter
open scoped Topology
namespace Preiss
variable {n m : ℕ}

theorem blowdown_gaussian_polynomial_limit (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (P : MvPolynomial (Fin n) ℝ) :
    ∃ l : ℝ, Tendsto (fun r : ℝ => ∫ z,
      MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖ ^ 2)
        ∂dimensionalBlowup m μ 0 r) atTop (𝓝 l) := by
  sorry

end Preiss
