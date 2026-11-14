import Preiss.Uniform.Scaling
import Preiss.Tangent.Normalization
import Preiss.Geometry.FlatMeasure
import FormalizingGMT.MarstrandTheorem

/-! # A common dimensional tangent normalization at a density point

The radius-power density q is fixed before choosing any tangent. This avoids
independently normalizing different tangents when applying a universal flatness gap.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- S08a uses the radius-power density; GMT's diameter density differs by 2^m. -/
theorem dimensionalTangent_ball_constant (hm : 0 < m)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) {q : ℝ} (hq : 0 < q)
    (hd : Tendsto (fun r : ℝ ↦ μ (closedBall x r) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal q)))
    (hu : ∀ ξ, IsTangentMeasure μ ξ x → IsSUniform (m : ℝ) ξ)
    (ν : Measure (Euclidean n)) (hν : IsDimensionalTangent m μ ν x) :
    IsUniformWithConstant m q ν ∧ (0 : Euclidean n) ∈ ν.support := by
  sorry

/-- S08b: identify the entire normalized tangent family, retaining its common factor. -/
theorem density_normalization_unitUniform (hm : 0 < m)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) {q : ℝ} (hq : 0 < q)
    (hd : Tendsto (fun r : ℝ ↦ μ (closedBall x r) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal q)))
    (hu : ∀ ξ, IsTangentMeasure μ ξ x → IsSUniform (m : ℝ) ξ) :
    (∀ ν, IsDimensionalTangent m ((ENNReal.ofReal q)⁻¹ • μ) ν x ↔
      IsDimensionalTangent m μ (ENNReal.ofReal q • ν) x) ∧
    (∀ ν, IsDimensionalTangent m ((ENNReal.ofReal q)⁻¹ • μ) ν x → IsUnitUniform m ν) ∧
    (∀ ν : Measure (Euclidean n), IsFlat m (ENNReal.ofReal q • ν) ↔ IsFlat m ν) := by
  sorry

end Preiss
