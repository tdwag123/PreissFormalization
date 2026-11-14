module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Bounds and extremizers for ordered finite sums -/

@[expose] public section
open scoped BigOperators
namespace Preiss

theorem ordered_nonnegative_trace_cutoff_bounds {m n : ℕ} (hm : 0 < m)
    (α : Fin n → ℝ) (horder : Antitone α) (hα : ∀ j, 0 ≤ α j)
    (htrace : ∑ j, α j = (m : ℝ)) (i : Fin n) (hi : i.val + 1 = m) :
    α i ≤ 1 ∧ ∀ j, α j - 1 ≤ ((m : ℝ) - 1) * (1 - α i) := by
  classical
  let s : Finset (Fin n) := Finset.Iic i
  have hcard : s.card = m := by simpa only [s, Fin.card_Iic] using hi
  have hsum : (∑ j ∈ s, α j) ≤ (m : ℝ) := by
    calc (∑ j ∈ s, α j) ≤ ∑ j, α j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun j _ _ => hα j)
      _ = (m : ℝ) := htrace
  have hbase : (m : ℝ) * α i ≤ (m : ℝ) := by
    calc (m : ℝ) * α i = ∑ j ∈ s, α i := by simp [hcard]
      _ ≤ ∑ j ∈ s, α j := Finset.sum_le_sum fun j hj => horder (Finset.mem_Iic.mp hj)
      _ ≤ (m : ℝ) := hsum
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hai : α i ≤ 1 := by nlinarith
  refine ⟨hai, ?_⟩
  intro j
  by_cases hj : j ∈ s
  · have hlow : ((s.erase j).card : ℝ) * α i ≤ ∑ k ∈ s.erase j, α k := by
      calc ((s.erase j).card : ℝ) * α i = ∑ k ∈ s.erase j, α i := by simp
        _ ≤ ∑ k ∈ s.erase j, α k := Finset.sum_le_sum fun k hk =>
          horder (Finset.mem_Iic.mp (Finset.mem_of_mem_erase hk))
    have hc : (s.erase j).card = m - 1 := by rw [Finset.card_erase_of_mem hj, hcard]
    rw [hc, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hlow
    have hsplit := Finset.sum_erase_add s α hj
    nlinarith
  · have hij : i ≤ j := le_of_lt (lt_of_not_ge (fun hji => hj (Finset.mem_Iic.mpr hji)))
    have haj : α j ≤ 1 := (horder hij).trans hai
    exact (sub_nonpos.mpr haj).trans (mul_nonneg (sub_nonneg.mpr hmone) (sub_nonneg.mpr hai))

theorem ordered_nonnegative_trace_eq_initial_indicator {m n : ℕ}
    (α : Fin n → ℝ) (horder : Antitone α) (hα : ∀ j, 0 ≤ α j)
    (htrace : ∑ j, α j = (m : ℝ)) (i : Fin n) (hi : i.val + 1 = m)
    (hai : α i = 1) : ∀ j, α j = if j.val < m then 1 else 0 := by
  classical
  let b (j : Fin n) : ℝ := if j.val < m then 1 else 0
  have hnonneg (j : Fin n) : 0 ≤ α j - b j := by
    dsimp [b]
    split_ifs with hj
    · have hji : j ≤ i := by change j.val ≤ i.val; omega
      have h := horder hji
      rw [hai] at h
      linarith
    · simpa using hα j
  have hset : Finset.univ.filter (fun j : Fin n => j.val < m) = Finset.Iic i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    change j.val < m ↔ j.val ≤ i.val
    omega
  have hsumB : ∑ j, b j = (m : ℝ) := by
    dsimp [b]
    rw [← Finset.sum_filter, hset]
    simp [Fin.card_Iic, hi]
  have hsumzero : (∑ j, (α j - b j)) = 0 := by
    rw [Finset.sum_sub_distrib, htrace, hsumB, sub_self]
  intro j
  have hle : α j - b j ≤ ∑ k, (α k - b k) :=
    Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
  rw [hsumzero] at hle
  have heq : α j = b j := by linarith [hnonneg j]
  exact heq

end Preiss

open scoped BigOperators
namespace Preiss

theorem antitone_weighted_sum_le_initial_sum {m n : ℕ}
    (α : Fin n → ℝ) (horder : Antitone α) (w : Fin n → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1) (hweight : ∑ j, w j = (m : ℝ))
    (i : Fin n) (hi : i.val + 1 = m) :
    (∑ j, α j * w j) ≤ ∑ j ∈ Finset.Iic i, α j := by
  classical
  let b (j : Fin n) : ℝ := if j ≤ i then 1 else 0
  have hset : Finset.univ.filter (fun j : Fin n => j ≤ i) = Finset.Iic i := by
    ext j
    simp
  have hsumB : ∑ j, b j = (m : ℝ) := by
    dsimp [b]
    rw [← Finset.sum_filter, hset]
    simp [Fin.card_Iic, hi]
  have hsumAB : (∑ j, α j * b j) = ∑ j ∈ Finset.Iic i, α j := by
    simp only [b, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, hset]
  have hterm (j : Fin n) : (α j - α i) * (w j - b j) ≤ 0 := by
    by_cases hj : j ≤ i
    · simp only [b, if_pos hj]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (horder hj))
        (sub_nonpos.mpr (hw1 j))
    · simp only [b, if_neg hj, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (horder (le_of_lt (lt_of_not_ge hj)))) (hw0 j)
  have hsum := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => hterm j)
  have hform (j : Fin n) : (α j - α i) * (w j - b j) =
      (α j * w j - α j * b j) - α i * (w j - b j) := by ring
  simp_rw [hform, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hweight, hsumB] at hsum
  rw [hsumAB] at hsum
  linarith

end Preiss
