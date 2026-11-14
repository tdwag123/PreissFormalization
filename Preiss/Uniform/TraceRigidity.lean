import Preiss.Uniform.RigidityErrorBounds
import Preiss.Uniform.RigidityPointwise
import Preiss.Uniform.RigidityErrorLimit
import Preiss.Uniform.RigidityError
import Preiss.Analysis.GaussianQuadraticForms

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Preiss
variable {n m : ℕ}

variable (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
  (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
  (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
  (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
  (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
  (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A)
include hm hμ hB hV hb hω hA

theorem adjustedForm_sq_le_norm_omega_sq (v : V.1) :
    (A v v) ^ 2 ≤ ‖b‖ ^ 2 * ‖ω v v‖ ^ 2 := by
  exact adjustedForm_sq_le_of_rigidityError_linear_growth μ hm hμ B hB V hV b hb ω A
    (rigidityError_le_linear_growth μ hm hμ B hB V hV b hb ω hω A hA) v

theorem adjustedForm_gaussian_error_tendsto_zero :
    Tendsto (fun s : ℝ => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * rigidityError V b ω A z ∂μ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  exact gaussian_rigidityError_limit_of_linear_growth μ hm hμ V b ω A
    (rigidityError_le_linear_growth μ hm hμ B hB V hV b hb ω hω A hA)

theorem integral_adjustedForm_sq_le :
    (∫ v : V.1, (A v v) ^ 2 ∂stdGaussian V.1) ≤
      -8 * ‖b‖ ^ 2 * ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  sorry

theorem integral_adjustedForm_lower_bound :
    -8 * (m : ℝ) * ‖b‖ ^ 2 / ((m : ℝ) + 2) ≤
      ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  sorry

theorem secondMomentCoefficient_trace_lower_bound :
    16 * ‖b‖ ^ 2 / ((m : ℝ) + 2) ≤ bilinearTrace (momentBilinear (B 2 2)) := by
  sorry

end Preiss
