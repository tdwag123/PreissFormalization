import Preiss.Uniform.FlatAtInfinity.TraceData
import Preiss.Analysis.GaussianQuadraticForms

open MeasureTheory ProbabilityTheory
namespace Preiss
variable {n m : ℕ}
variable (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
  (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
  (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
  (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
  (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
include hm hμ hB hV hb hω

theorem integral_rigidityOmega_eq_zero :
    (∫ v : V.1, ω v v ∂stdGaussian V.1) = 0 := by
  sorry

theorem trace_tangent_eq_integral_adjustedForm
    (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A) :
    bilinearTrace (restrictBilinear (momentBilinear (B 2 2)) V.1) =
      ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  sorry

theorem integral_inner_sq_mul_omega (y : V.1) (w : V.1ᗮ) :
    (∫ v : V.1, (inner ℝ y v) ^ 2 * inner ℝ (ω v v) w ∂stdGaussian V.1) =
      2 * inner ℝ (ω y y) w := by
  sorry

end Preiss
