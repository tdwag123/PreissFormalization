module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! # Derivatives at zero of a quadratic exponential

Leibniz's rule gives the derivative of `t * f t` at zero. Applied to the
quadratic exponential differential equation, it gives every even derivative.
-/

open scoped BigOperators
namespace Preiss

theorem iteratedDeriv_id_mul_zero {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ n f 0) :
    iteratedDeriv n (fun t => t * f t) 0 = n * iteratedDeriv (n - 1) f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf]
  simp only [iteratedDeriv_fun_id_zero]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b hb hb1
    simp [hb1]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem iteratedDeriv_exp_quadratic_even (a : ℝ) (j : ℕ) :
    iteratedDeriv (2 * j) (fun t : ℝ => Real.exp (a * t ^ 2 / 2)) 0 =
      ((2 * j).factorial : ℝ) / (2 ^ j * (j.factorial : ℝ)) * a ^ j := by
  let f : ℝ → ℝ := fun t => Real.exp (a * t ^ 2 / 2)
  have hd : deriv f = fun t => a * (t * f t) := by
    funext t
    have h := (((hasDerivAt_id t).pow 2).const_mul a).div_const 2
    have h' := h.exp
    convert h'.deriv using 1 <;> dsimp [f] <;> ring
  have hsmooth (k : ℕ) : ContDiffAt ℝ k f 0 := by dsimp [f]; fun_prop
  change iteratedDeriv (2 * j) f 0 = _
  induction j with
  | zero => simp [f]
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, iteratedDeriv_succ', hd,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_id_mul_zero (by omega) f (hsmooth _)]
    simp only [Nat.add_sub_cancel, ih]
    rw [show (2 * j + 1 + 1).factorial =
      (2 * j + 2) * (2 * j + 1) * (2 * j).factorial by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
    rw [Nat.factorial_succ, pow_succ, pow_succ]
    push_cast
    have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ j ≠ 0 := by positivity
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring

end Preiss
