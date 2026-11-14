import Preiss.Uniform.FlatAtInfinity.Basic
import Preiss.Uniform.MixedMomentBounds
import Preiss.Analysis.MultilinearDiagonal
import Preiss.Uniform.MomentExpansion
import Preiss.Uniform.TraceRigidity
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

namespace Preiss
open MeasureTheory
variable {n m : ℕ}
variable (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
  (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
  (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
include hm hμ hB hV

theorem thirdMomentCoefficient_normal_vanishes_draft (v : V.1) (w : V.1ᗮ) :
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

theorem fourth_order_support_identity_draft (z : Euclidean n) (hz : z ∈ μ.support) :
    B 1 2 (fun _ => z) + B 2 2 ![z, z] +
      3 * B 3 2 ![proj V z, proj V z, z - proj V z] =
      ‖z - proj V z‖ ^ 4 + 2 * ‖proj V z‖ ^ 2 * ‖z - proj V z‖ ^ 2 := by
  let v : V.1 := V.1.orthogonalProjectionOnto z
  let w : V.1ᗮ := ⟨z - proj V z, V.1.sub_starProjection_mem_orthogonal z⟩
  obtain ⟨hplane, htwo, hnormal⟩ :=
    thirdMomentCoefficient_normal_vanishes_draft μ hm hμ B hB V hV v w
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

#print axioms Preiss.thirdMomentCoefficient_normal_vanishes_draft
#print axioms Preiss.fourth_order_support_identity_draft

namespace Preiss

theorem norm_bilinear_diagonal_sub_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E →L[ℝ] E →L[ℝ] F) (z p : E) :
    ‖Q z z - Q p p‖ ≤ ‖Q‖ * ‖z-p‖ * (‖z‖+‖p‖) := by
  have heq : Q z z - Q p p = Q (z-p) z + Q p (z-p) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  calc
    _ ≤ ‖Q (z-p) z‖ + ‖Q p (z-p)‖ := norm_add_le _ _
    _ ≤ ‖Q‖ * ‖z-p‖ * ‖z‖ + ‖Q‖ * ‖p‖ * ‖z-p‖ :=
      add_le_add (Q.le_opNorm₂ (z-p) z) (Q.le_opNorm₂ p (z-p))
    _ = _ := by ring

end Preiss
#print axioms Preiss.norm_bilinear_diagonal_sub_le

namespace Preiss
variable {n m : ℕ}

theorem rigidityError_eq_coefficient_remainder
    (B : MomentCoefficientFamily n) (V : Plane m n) (b : V.1ᗮ)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
    (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A)
    (z : Euclidean n)
    (hnormal : ‖z-proj V z‖^2 = 2 * inner ℝ (b : Euclidean n) z)
    (hfour : B 1 2 (fun _ => z) + B 2 2 ![z,z] +
      3 * B 3 2 ![proj V z,proj V z,z-proj V z] =
        ‖z-proj V z‖^4 + 2*‖proj V z‖^2*‖z-proj V z‖^2) :
    rigidityError V b ω A z = ‖z-proj V z‖^4 - B 1 2 (fun _ => z) -
      (B 2 2 ![z,z] - B 2 2 ![proj V z,proj V z]) := by
  let p : V.1 := V.1.orthogonalProjectionOnto z
  let w : V.1ᗮ := ⟨z-proj V z,V.1.sub_starProjection_mem_orthogonal z⟩
  have hbp : inner ℝ (b : Euclidean n) (proj V z) = 0 :=
    V.1.inner_left_of_mem_orthogonal p.property b.property
  have hω' := hω.2 p p w
  change inner ℝ (ω p p : Euclidean n) (z-proj V z) =
    3 * B 3 2 ![proj V z,proj V z,z-proj V z] -
      4 * inner ℝ (proj V z) (proj V z) *
        inner ℝ (b : Euclidean n) (z-proj V z) at hω'
  rw [real_inner_self_eq_norm_sq,inner_sub_right,hbp,sub_zero] at hω'
  have hA' := hA.2 p p
  change A p p = B 2 2 ![proj V z,proj V z] +
    inner ℝ (ω p p : Euclidean n) (b : Euclidean n) at hA'
  change A p p + inner ℝ (ω p p : Euclidean n)
    (z-proj V z-(b : Euclidean n)) = _
  rw [inner_sub_right,hA',hω']
  have hcancel := congrArg (fun t : ℝ => 2 * ‖proj V z‖^2 * t) hnormal
  nlinarith [hfour]

end Preiss
#print axioms Preiss.rigidityError_eq_coefficient_remainder

namespace Preiss
open MeasureTheory
variable {n m : ℕ}

theorem rigidityError_le_linear_growth_draft
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
    (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ μ.support,
      |rigidityError V b ω A z| ≤ C * (1 + ‖z‖) := by
  let R : ℝ := 2 * ‖b‖
  let Q := momentBilinear (B 2 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ (u v : Euclidean n) : Q u v = B 2 2 ![u,v] := by
    change B 2 2 (Fin.cons u (fun _ => v)) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  refine ⟨R^4 + ‖B 1 2‖ + 2*‖Q‖*R, by positivity, ?_⟩
  intro z hz
  have hcylinder := support_normal_sq_eq_inner μ hm hμ B hB V hV b hb z hz
  have hnormal : ‖z-proj V z‖ ≤ R := hcylinder.2.2
  have hp : ‖proj V z‖ ≤ ‖z‖ := V.1.norm_orthogonalProjectionOnto_apply_le z
  have herr := rigidityError_eq_coefficient_remainder B V b ω hω A hA z
    hcylinder.1 (fourth_order_support_identity_draft μ hm hμ B hB V hV z hz)
  have hlinear : |B 1 2 (fun _ => z)| ≤ ‖B 1 2‖ * ‖z‖ := by
    simpa only [Real.norm_eq_abs,Finset.prod_const,Finset.card_univ,
      Fintype.card_fin,pow_one] using (B 1 2).le_opNorm (fun _ => z)
  have hquadratic : |B 2 2 ![z,z] - B 2 2 ![proj V z,proj V z]| ≤
      2*‖Q‖*R*‖z‖ := by
    calc
      _ = ‖Q z z - Q (proj V z) (proj V z)‖ := by rw [hQ,hQ,Real.norm_eq_abs]
      _ ≤ ‖Q‖ * ‖z-proj V z‖ * (‖z‖+‖proj V z‖) :=
        norm_bilinear_diagonal_sub_le Q z (proj V z)
      _ ≤ (‖Q‖*R) * (2*‖z‖) := mul_le_mul
        (mul_le_mul_of_nonneg_left hnormal (norm_nonneg _))
        (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hfour : ‖z-proj V z‖^4 ≤ R^4 :=
    pow_le_pow_left₀ (norm_nonneg _) hnormal 4
  rw [herr]
  calc
    _ ≤ |‖z-proj V z‖^4 - B 1 2 (fun _ => z)| +
        |B 2 2 ![z,z] - B 2 2 ![proj V z,proj V z]| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (‖z-proj V z‖^4 - B 1 2 (fun _ => z))
        (B 2 2 ![z,z] - B 2 2 ![proj V z,proj V z])
    _ ≤ (‖z-proj V z‖^4 + |B 1 2 (fun _ => z)|) +
        |B 2 2 ![z,z] - B 2 2 ![proj V z,proj V z]| := by
      apply add_le_add_right
      simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity :
        0 ≤ ‖z-proj V z‖^4)] using norm_sub_le
          (‖z-proj V z‖^4) (B 1 2 (fun _ => z))
    _ ≤ (R^4 + ‖B 1 2‖*‖z‖) + 2*‖Q‖*R*‖z‖ :=
      add_le_add (add_le_add hfour hlinear) hquadratic
    _ ≤ _ := by
      have hQR : 0 ≤ 2*‖Q‖*R := by positivity
      nlinarith [norm_nonneg (B 1 2),mul_nonneg (pow_nonneg hR 4) (norm_nonneg z)]

end Preiss

#print axioms Preiss.rigidityError_le_linear_growth_draft
