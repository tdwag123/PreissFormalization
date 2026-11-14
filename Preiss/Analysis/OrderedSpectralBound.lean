module

public import Preiss.Analysis.OrderedSums
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
open scoped BigOperators
namespace Preiss

theorem orthonormal_diagonal_sum_le_initial_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m n : ℕ} {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis (Fin n) ℝ E) (v : ι → E) (hv : Orthonormal ℝ v)
    (hcard : Fintype.card ι = m) (α : Fin n → ℝ) (horder : Antitone α)
    (i : Fin n) (hi : i.val + 1 = m) :
    (∑ a, ∑ j, α j * (inner ℝ (v a) (e j)) ^ 2) ≤ ∑ j ∈ Finset.Iic i, α j := by
  classical
  let w (j : Fin n) : ℝ := ∑ a, (inner ℝ (v a) (e j)) ^ 2
  have hw0 (j : Fin n) : 0 ≤ w j := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hw1 (j : Fin n) : w j ≤ 1 := by
    have h := hv.sum_inner_products_le (s := Finset.univ) (e j)
    simpa only [w, Real.norm_eq_abs, sq_abs, e.norm_eq_one, one_pow] using h
  have hweight : ∑ j, w j = (m : ℝ) := by
    dsimp only [w]
    rw [Finset.sum_comm]
    simp_rw [e.sum_sq_inner_left, hv.norm_eq_one, one_pow]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  calc
    (∑ a, ∑ j, α j * (inner ℝ (v a) (e j)) ^ 2) = ∑ j, α j * w j := by
      rw [Finset.sum_comm]
      simp only [w, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.Iic i, α j :=
      antitone_weighted_sum_le_initial_sum α horder w hw0 hw1 hweight i hi

end Preiss
