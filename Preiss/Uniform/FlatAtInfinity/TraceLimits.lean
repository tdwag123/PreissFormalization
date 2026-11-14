import Preiss.Uniform.FlatAtInfinity.TraceData

open MeasureTheory Filter Set
open scoped Topology
namespace Preiss
variable {n m : ℕ}
variable (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
  (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
  (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
  (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
include hm hμ hB hV hb

theorem mixed_gaussian_limit_eq_omega (v w : Euclidean n) :
    Tendsto (fun s : ℝ => (8 * s / gaussianMass μ s) *
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * (inner ℝ z v) ^ 2 *
        inner ℝ (z - (b : Euclidean n)) w ∂μ)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (3 * B 3 2 ![v, v, w] -
        4 * B 2 1 ![v, v] * inner ℝ (b : Euclidean n) w)) := by
  sorry

theorem contracted_gaussian_limit_eq_zero (w : V.1ᗮ) :
    Tendsto (fun s : ℝ => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s * ‖z‖ ^ 2) * ‖proj V z‖ ^ 2 *
        inner ℝ (z - (b : Euclidean n)) (w : Euclidean n) ∂μ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  sorry

end Preiss
