import Preiss.Uniform.FlatAtInfinity.Basic
import Preiss.Uniform.SubspaceMomentCoefficients
import Mathlib.Tactic
open MeasureTheory
namespace Preiss
variable {m n : ℕ}
theorem trace_secondMomentCoefficient_normal_eq_checked
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b) :
    bilinearTrace (restrictBilinear (momentBilinear (B 2 2)) V.1ᗮ) = 8 * ‖b‖ ^ 2 := by
  letI : μ.Regular := hμ.1
  have hcyl : ∀ᵐ z ∂μ, ‖V.1ᗮ.starProjection z‖ ^ 2 = 2 * inner ℝ (b : Euclidean n) z := by
    filter_upwards [μ.support_mem_ae] with z hz
    rw [V.1.starProjection_orthogonal_val]
    exact (support_normal_sq_eq_inner μ hm hμ B hB V hV b hb z hz).1
  rw [subspaceTrace_secondCoefficient_of_cylinder μ hm hμ B hB V.1ᗮ b hcyl,
    hb b, real_inner_self_eq_norm_sq]
  change (4 : ℝ) * (2 * ‖b‖^2) = 8 * ‖b‖^2
  ring
end Preiss
#print axioms Preiss.trace_secondMomentCoefficient_normal_eq_checked
