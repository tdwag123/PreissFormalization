module
public import Preiss.Geometry.Euclidean
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Tactic

@[expose] public section
namespace Preiss

theorem exists_polynomial_norm_bound_outside_unit_ball {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ z : Euclidean n, 1 ≤ ‖z‖ →
      ‖MvPolynomial.eval (fun j => z j) P‖ ≤ C * ‖z‖ ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      exact ⟨‖a‖, norm_nonneg _, 0, by simp⟩
  | add P Q hP hQ =>
      obtain ⟨C, hC, d, hd⟩ := hP
      obtain ⟨D, hD, e, he⟩ := hQ
      refine ⟨C + D, add_nonneg hC hD, d + e, ?_⟩
      intro z hz
      simp only [MvPolynomial.eval_add]
      calc
        _ ≤ ‖MvPolynomial.eval (fun j => z j) P‖ + ‖MvPolynomial.eval (fun j => z j) Q‖ := norm_add_le _ _
        _ ≤ C * ‖z‖ ^ d + D * ‖z‖ ^ e := add_le_add (hd z hz) (he z hz)
        _ ≤ C * ‖z‖ ^ (d + e) + D * ‖z‖ ^ (d + e) := add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (Nat.le_add_right d e)) hC)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (Nat.le_add_left e d)) hD)
        _ = _ := by ring
  | mul_X P i hP =>
      obtain ⟨C, hC, d, hd⟩ := hP
      refine ⟨C, hC, d + 1, ?_⟩
      intro z hz
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, norm_mul]
      calc
        _ ≤ C * ‖z‖ ^ d * ‖z‖ := mul_le_mul (hd z hz) (PiLp.norm_apply_le z i)
          (norm_nonneg _) (mul_nonneg hC (pow_nonneg (norm_nonneg _) _))
        _ = _ := by rw [pow_succ]; ring

end Preiss
