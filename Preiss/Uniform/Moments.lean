import Preiss.Tangent.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory
open scoped BigOperators

namespace Preiss

variable {n : ℕ}

/-- Scalar evaluation of the Gaussian moment tensor (De Lellis 7.4).
Integrability and the continuous multilinear packaging are separate lemmas. -/
noncomputable def gaussianMoment (μ : Measure (Euclidean n)) (k : ℕ)
    (s : ℝ) (u : Fin k → Euclidean n) : ℝ :=
  (2 * s) ^ k / (Nat.factorial k : ℝ) *
    (∫ z, Real.exp (-s * ‖z‖ ^ 2) ∂μ)⁻¹ *
    ∫ z, (∏ i, inner ℝ z (u i)) * Real.exp (-s * ‖z‖ ^ 2) ∂μ

end Preiss
