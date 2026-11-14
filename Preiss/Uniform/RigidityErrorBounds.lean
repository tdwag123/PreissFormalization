import Preiss.Uniform.RigidityError
import Mathlib.Tactic

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


end Preiss
