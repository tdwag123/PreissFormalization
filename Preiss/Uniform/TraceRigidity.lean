import Preiss.Uniform.RigidityContraction
import Preiss.Uniform.FlatAtInfinity.TraceIdentities
import Preiss.Analysis.GaussianRigidityBounds
import Preiss.Analysis.OrthogonalTraceSplit
import Mathlib.Tactic
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
  have hmean := rigidityOmega_contraction_of_mean_zero_and_error_limit μ hm hμ B hB V hV b hb ω hω A
    (integral_rigidityOmega_eq_zero μ hm hμ B hB V hV b hb ω hω)
    (adjustedForm_gaussian_error_tendsto_zero μ hm hμ B hB V hV b hb ω hω A hA)
  exact (gaussian_quadratic_bounds_of_mean_square_identity A hA.1 ω
    (by rw [V.2]; exact hm) (‖b‖^2) (sq_nonneg _)
    (adjustedForm_sq_le_norm_omega_sq μ hm hμ B hB V hV b hb ω hω A hA) hmean).1

theorem integral_adjustedForm_lower_bound :
    -8 * (m : ℝ) * ‖b‖ ^ 2 / ((m : ℝ) + 2) ≤
      ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  have h := gaussian_bilinear_integral_lower_bound_of_square_upper A hA.1
    (by rw [V.2]; exact hm) (‖b‖^2) (sq_nonneg _)
    (integral_adjustedForm_sq_le μ hm hμ B hB V hV b hb ω hω A hA)
  simpa only [V.2] using h

theorem secondMomentCoefficient_trace_lower_bound :
    16 * ‖b‖ ^ 2 / ((m : ℝ) + 2) ≤ bilinearTrace (momentBilinear (B 2 2)) := by
  have hnormal := trace_secondMomentCoefficient_normal_eq μ hm hμ B hB V hV b hb
  have htangent := trace_tangent_eq_integral_adjustedForm μ hm hμ B hB V hV b hb ω hω A hA
  have hlower := integral_adjustedForm_lower_bound μ hm hμ B hB V hV b hb ω hω A hA
  rw [bilinearTrace_eq_restrict_add_orthogonal _ V.1, hnormal, htangent]
  have hd : 0 < (m:ℝ)+2 := by positivity
  apply (div_le_iff₀ hd).mpr
  have h := (div_le_iff₀ hd).mp hlower
  nlinarith

end Preiss
