import Preiss.Uniform.FlatAtInfinity.SupportIdentity
import Preiss.Uniform.RigidityErrorBounds
import Preiss.Analysis.BilinearDiagonalDifference
import Mathlib.Tactic

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
      have ht : |‖z-proj V z‖^4 - B 1 2 (fun _ => z)| ≤
          |‖z-proj V z‖^4| + |B 1 2 (fun _ => z)| := by
        simpa only [Real.norm_eq_abs] using
          norm_sub_le (‖z-proj V z‖^4) (B 1 2 (fun _ => z))
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg (z-proj V z)) 4)] at ht
      exact ht
    _ ≤ (R^4 + ‖B 1 2‖*‖z‖) + 2*‖Q‖*R*‖z‖ :=
      add_le_add (add_le_add hfour hlinear) hquadratic
    _ ≤ _ := by
      have hQR : 0 ≤ 2*‖Q‖*R := by positivity
      nlinarith [norm_nonneg (B 1 2),mul_nonneg (pow_nonneg hR 4) (norm_nonneg z)]

end Preiss

#print axioms Preiss.rigidityError_le_linear_growth_draft
