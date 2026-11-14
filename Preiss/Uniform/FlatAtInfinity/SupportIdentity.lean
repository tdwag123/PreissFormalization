import Preiss.Uniform.FlatAtInfinity.Basic
import Preiss.Uniform.MixedMomentBounds
import Preiss.Analysis.MultilinearDiagonal
import Preiss.Uniform.MomentExpansion
import Mathlib.Tactic

namespace Preiss
open MeasureTheory
variable {n m : ℕ}
variable (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
  (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
  (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
include hm hμ hB hV

theorem thirdMomentCoefficient_normal_vanishes (v : V.1) (w : V.1ᗮ) :
    B 3 2 ![(v : Euclidean n), (v : Euclidean n), (v : Euclidean n)] = 0 ∧
    B 3 2 ![(v : Euclidean n), (w : Euclidean n), (w : Euclidean n)] = 0 ∧
    B 3 2 ![(w : Euclidean n), (w : Euclidean n), (w : Euclidean n)] = 0 := by
  obtain ⟨b, hb⟩ := exists_firstMomentNormalVector μ hm hμ B hB V hV
  have htube (z : Euclidean n) (hz : z ∈ μ.support) :
      ‖z - V.1.starProjection z‖ ≤ 2 * ‖b‖ :=
    (support_normal_sq_eq_inner μ hm hμ B hB V hV b hb z hz).2.2
  refine ⟨?_, thirdMomentCoefficient_two_normal_eq_zero_of_bounded_tube
    μ hm hμ B hB V.1 (2 * ‖b‖) (by positivity) htube v w,
    thirdMomentCoefficient_two_normal_eq_zero_of_bounded_tube
    μ hm hμ B hB V.1 (2 * ‖b‖) (by positivity) htube w w⟩
  have h := oddMomentCoefficient_restrict_plane_eq_zero μ hm hμ B hB V hV
    2 (by decide) (fun _ => v)
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

theorem fourth_order_support_identity (z : Euclidean n) (hz : z ∈ μ.support) :
    B 1 2 (fun _ => z) + B 2 2 ![z, z] +
      3 * B 3 2 ![proj V z, proj V z, z - proj V z] =
      ‖z - proj V z‖ ^ 4 + 2 * ‖proj V z‖ ^ 2 * ‖z - proj V z‖ ^ 2 := by
  let v : V.1 := V.1.orthogonalProjectionOnto z
  let w : V.1ᗮ := ⟨z - proj V z, V.1.sub_starProjection_mem_orthogonal z⟩
  obtain ⟨hplane, htwo, hnormal⟩ :=
    thirdMomentCoefficient_normal_vanishes μ hm hμ B hB V hV v w
  have hcube := symmetricTrilinear_diagonal_add (B 3 2) (hB.1 3 2)
    (proj V z) (z - proj V z)
  have hsplit : proj V z + (z - proj V z) = z := by abel
  rw [hsplit] at hcube
  change B 3 2 ![proj V z, proj V z, proj V z] = 0 at hplane
  change B 3 2 ![proj V z, z - proj V z, z - proj V z] = 0 at htwo
  change B 3 2 ![z - proj V z, z - proj V z, z - proj V z] = 0 at hnormal
  rw [hplane, htwo, hnormal] at hcube
  simp only [mul_zero, add_zero, zero_add] at hcube
  have hsum := sum_gaussianMomentCoefficient_eq_norm_pow μ hm hμ B hB 2 (by decide) z hz
  have heven := evenMomentCoefficient_eq_projection_norm μ hm hμ B hB V hV 2 (by decide) z
  norm_num [Finset.sum_range_succ] at hsum heven
  have hdiag₂ : B 2 2 (fun _ => z) = B 2 2 ![z,z] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  have hdiag₃ : B 3 2 (fun _ => z) = B 3 2 ![z,z,z] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [heven, hdiag₂, hdiag₃, hcube] at hsum
  have hnorm := Submodule.norm_sq_eq_add_norm_sq_starProjection z V.1
  rw [V.1.starProjection_orthogonal_val] at hnorm
  change ‖z‖^2 = ‖proj V z‖^2 + ‖z-proj V z‖^2 at hnorm
  have hfour : ‖z‖^4 = ‖proj V z‖^4 +
      2 * ‖proj V z‖^2 * ‖z-proj V z‖^2 + ‖z-proj V z‖^4 := by
    calc
      _ = (‖z‖^2)^2 := by ring
      _ = _ := by rw [hnorm]; ring
  linarith

end Preiss
