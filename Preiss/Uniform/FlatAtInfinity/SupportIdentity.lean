import Preiss.Uniform.FlatAtInfinity.TraceData

open MeasureTheory
namespace Preiss
variable {n m : ℕ}
variable (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
  (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
  (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
include hm hμ hB hV

theorem thirdMomentCoefficient_normal_vanishes (v : V.1) (w : V.1ᗮ) :
    B 3 2 ![(v : Euclidean n), (v : Euclidean n), (v : Euclidean n)] = 0 ∧
    B 3 2 ![(v : Euclidean n), (w : Euclidean n), (w : Euclidean n)] = 0 ∧
    B 3 2 ![(w : Euclidean n), (w : Euclidean n), (w : Euclidean n)] = 0 := by
  sorry

theorem fourth_order_support_identity (z : Euclidean n) (hz : z ∈ μ.support) :
    B 1 2 (fun _ => z) + B 2 2 ![z, z] +
      3 * B 3 2 ![proj V z, proj V z, z - proj V z] =
      ‖z - proj V z‖ ^ 4 + 2 * ‖proj V z‖ ^ 2 * ‖z - proj V z‖ ^ 2 := by
  sorry

end Preiss
