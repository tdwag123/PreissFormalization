import Preiss.Analysis.AsymptoticCoefficients
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Tactic

open Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem taylorCoefficient_eq_of_exact_monomial
    (f : ℝ → F) (A : ℕ → F) (a : F) (d : ℕ) (hd : 0 < d)
    (hf : ∀ s : ℝ, 0 < s → f s = s ^ d • a)
    (hA : ∀ q : ℕ, 0 < q → IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => f s - ∑ i ∈ Finset.range q, s ^ (i+1) • A (i+1))
      (fun s : ℝ => s ^ q)) :
    ∀ j : ℕ, 0 < j → A j = if j = d then a else 0 := by
  classical
  let C : ℕ → F := fun j => if j = d then a else 0
  have hpoly (q : ℕ) (s : ℝ) :
      (∑ i ∈ Finset.range q, s ^ (i+1) • C (i+1)) =
        if d ≤ q then s ^ d • a else 0 := by
    by_cases hq : d ≤ q
    · rw [if_pos hq, Finset.sum_eq_single (d-1)]
      · simp only [show d-1+1=d by omega, C, if_pos rfl]
      · intro i hi hne
        have hne' : i+1 ≠ d := by omega
        simp only [C, if_neg hne', smul_zero]
      · intro hn
        exact (hn (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg hq]
      apply Finset.sum_eq_zero
      intro i hi
      have hne : i+1 ≠ d := by have := Finset.mem_range.mp hi; omega
      simp only [C, if_neg hne, smul_zero]
  have hC (q : ℕ) (hq : 0 < q) : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => f s - ∑ i ∈ Finset.range q, s ^ (i+1) • C (i+1))
      (fun s : ℝ => s ^ q) := by
    have hm : IsLittleO (𝓝[>] (0 : ℝ))
        (fun s => s ^ d • a - (if d ≤ q then s ^ d • a else 0))
        (fun s : ℝ => s ^ q) := by
      by_cases hle : d ≤ q
      · simp only [hle, if_true, sub_self]
        exact isLittleO_zero _ _
      · simp only [hle, if_false, sub_zero]
        have hb : IsBigO (𝓝[>] (0 : ℝ)) (fun s : ℝ => s ^ d • a)
            (fun s : ℝ => s ^ d) := by
          apply IsBigO.of_bound ‖a‖
          exact Filter.Eventually.of_forall (fun s => by simp only [norm_smul]; rw [mul_comm])
        apply hb.trans_isLittleO
        simpa only [Real.rpow_natCast] using
          isLittleO_rpow_nhdsGT_zero (a := (d : ℝ)) (b := (q : ℝ))
            (Nat.cast_lt.mpr (by omega))
    apply hm.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hf s hs, hpoly]
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hprev (s : ℝ) : (∑ i ∈ Finset.range q, s ^ (i+1) • A (i+1)) =
        ∑ i ∈ Finset.range q, s ^ (i+1) • C (i+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (i+1) (by have := Finset.mem_range.mp hi; omega) (by omega)]
    have hdiff := (hC (q+1) (by omega)).sub (hA (q+1) (by omega))
    have hsmall : IsLittleO (𝓝[>] (0 : ℝ))
        (fun s : ℝ => s ^ (q+1) • (A (q+1) - C (q+1)))
        (fun s : ℝ => s ^ (q+1)) := by
      convert hdiff using 1
      funext s
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hprev]
      simp only [smul_sub]
      abel
    exact sub_eq_zero.mp (eq_zero_of_isLittleO_pow_smul (q+1) (A (q+1)-C (q+1)) hsmall)

end Preiss
#print axioms Preiss.taylorCoefficient_eq_of_exact_monomial
