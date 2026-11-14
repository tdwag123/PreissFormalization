import Preiss.Uniform.FlatAtInfinity.SupportIdentity
import Preiss.Analysis.BilinearDiagonalDifference
import Preiss.Uniform.RigidityError
import Mathlib.Tactic

open MeasureTheory
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
  have hbw : inner ℝ (b : Euclidean n) (z-proj V z) = inner ℝ (b : Euclidean n) z := by
    rw [inner_sub_right,hbp,sub_zero]
  rw [real_inner_self_eq_norm_sq,hbw] at hω'
  have hA' := hA.2 p p
  change A p p = B 2 2 ![proj V z,proj V z] +
    inner ℝ (ω p p : Euclidean n) (b : Euclidean n) at hA'
  change A p p + inner ℝ (ω p p : Euclidean n)
    (z-proj V z-(b : Euclidean n)) = _
  rw [inner_sub_right,hA',hω']
  have hcancel := congrArg (fun t : ℝ => 2 * ‖proj V z‖^2 * t) hnormal
  nlinarith [hfour]


theorem rigidityError_le_linear_growth
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
    hcylinder.1 (fourth_order_support_identity μ hm hμ B hB V hV z hz)
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
        (mul_le_mul_of_nonneg_left hnormal (norm_nonneg Q))
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
      apply add_le_add _ le_rfl
      apply abs_le.mpr
      constructor <;> nlinarith [le_abs_self (B 1 2 (fun _ => z)),
        neg_abs_le (B 1 2 (fun _ => z)),pow_nonneg (norm_nonneg (z-proj V z)) 4]
    _ ≤ (R^4 + ‖B 1 2‖*‖z‖) + 2*‖Q‖*R*‖z‖ :=
      add_le_add (add_le_add hfour hlinear) hquadratic
    _ ≤ _ := by
      have hQR : 0 ≤ 2*‖Q‖*R := by positivity
      nlinarith [norm_nonneg (B 1 2),mul_nonneg (pow_nonneg hR 4) (norm_nonneg z)]

end Preiss
