module

public import Preiss.Analysis.OrderedSums
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Rigidity of a quadratic identity near a critical eigenvector -/

@[expose] public section
open scoped BigOperators
namespace Preiss

theorem ordered_quadratic_identity_rigid_of_near_basis_vector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m n : ℕ}
    (hm : 0 < m) (e : OrthonormalBasis (Fin n) ℝ E)
    (α : Fin n → ℝ) (horder : Antitone α) (hα : ∀ j, 0 ≤ α j)
    (htrace : ∑ j, α j = (m : ℝ)) (i : Fin n) (hi : i.val + 1 = m)
    (δ : ℝ) (hδ : 0 < δ) (hδm : δ < 1 / (m : ℝ))
    (x : E) (hx : (∑ j, α j * (inner ℝ x (e j)) ^ 2) = ‖x‖ ^ 2)
    (hnear : dist x (e i) < δ) :
    ∀ j, α j = if j.val < m then 1 else 0 := by
  classical
  obtain ⟨hai, hbound⟩ := ordered_nonnegative_trace_cutoff_bounds hm α horder hα htrace i hi
  apply ordered_nonnegative_trace_eq_initial_indicator α horder hα htrace i hi
  by_contra hne
  have haiLt : α i < 1 := lt_of_le_of_ne hai hne
  let β : ℝ := 1 - α i
  have hβ : 0 < β := sub_pos.mpr haiLt
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hδmul : δ * (m : ℝ) < 1 := (lt_div_iff₀ hmR).mp hδm
  have hδone : δ < 1 := by nlinarith
  let t (j : Fin n) : ℝ := inner ℝ x (e j)
  have hquad : (∑ j, (α j - 1) * (t j) ^ 2) = 0 := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, t]
    rw [hx, e.sum_sq_inner_left, sub_self]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => (α j - 1) * (t j) ^ 2)
    (Finset.mem_univ i)
  rw [hquad] at hsum
  have hupper : (∑ j ∈ Finset.univ.erase i, (α j - 1) * (t j) ^ 2) ≤
      (((m : ℝ) - 1) * β) * (∑ j ∈ Finset.univ.erase i, (t j) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hbound j) (sq_nonneg _)
  have hrest : (∑ j ∈ Finset.univ.erase i, (t j) ^ 2) ≤ ‖x - e i‖ ^ 2 := by
    calc
      (∑ j ∈ Finset.univ.erase i, (t j) ^ 2) =
          ∑ j ∈ Finset.univ.erase i, (inner ℝ (x - e i) (e j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have heij : inner ℝ (e i) (e j) = 0 := by
          simpa only [if_neg hji.symm] using (orthonormal_iff_ite.mp e.orthonormal i j)
        dsimp only [t]
        rw [inner_sub_left, heij, sub_zero]
      _ ≤ ∑ j, (inner ℝ (x - e i) (e j)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => sq_nonneg _)
      _ = ‖x - e i‖ ^ 2 := e.sum_sq_inner_left _
  have hQ : β * (t i) ^ 2 ≤ (((m : ℝ) - 1) * β) * ‖x - e i‖ ^ 2 := by
    calc
      β * (t i) ^ 2 = ∑ j ∈ Finset.univ.erase i, (α j - 1) * (t j) ^ 2 := by
        dsimp only [β]
        nlinarith [hsum]
      _ ≤ (((m : ℝ) - 1) * β) * (∑ j ∈ Finset.univ.erase i, (t j) ^ 2) := hupper
      _ ≤ (((m : ℝ) - 1) * β) * ‖x - e i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hrest (mul_nonneg (sub_nonneg.mpr hmone) hβ.le)
  have hcancel : (t i) ^ 2 ≤ ((m : ℝ) - 1) * ‖x - e i‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hβ).mp
    convert hQ using 1 <;> ring
  have hd : ‖x - e i‖ < δ := by simpa only [dist_eq_norm] using hnear
  have hinner : |t i - 1| ≤ ‖x - e i‖ := by
    have h := abs_real_inner_le_norm (x - e i) (e i)
    simpa only [inner_sub_left, real_inner_self_eq_norm_sq, e.norm_eq_one,
      one_pow, mul_one, t] using h
  have hti : 1 - δ < t i := by
    have h := (abs_le.mp hinner).1
    linarith
  have htiSq : (1 - δ) ^ 2 < (t i) ^ 2 := by nlinarith
  have hdSq : ‖x - e i‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd.le 2
  have hfinal : (t i) ^ 2 ≤ ((m : ℝ) - 1) * δ ^ 2 :=
    hcancel.trans (mul_le_mul_of_nonneg_left hdSq (sub_nonneg.mpr hmone))
  have hgap : ((m : ℝ) - 1) * δ ^ 2 < (1 - δ) ^ 2 := by
    by_cases hm1 : m = 1
    · simp only [hm1, Nat.cast_one, sub_self, zero_mul]
      exact pow_pos (sub_pos.mpr hδone) 2
    · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      have hδhalf : δ < 1 / 2 := by nlinarith
      have hA : ((m : ℝ) - 1) * δ < 1 - δ := by nlinarith
      have hB := mul_lt_mul_of_pos_right hA hδ
      nlinarith
  linarith

end Preiss
