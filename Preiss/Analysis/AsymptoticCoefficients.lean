module
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Arith
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

open Filter Set Asymptotics
open scoped Topology
@[expose] public section
namespace Preiss

theorem isLittleO_rpow_nhdsGT_zero {a b : ℝ} (h : b < a) :
    IsLittleO (𝓝[>] (0 : ℝ)) (fun s : ℝ => s ^ a) (fun s : ℝ => s ^ b) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact fun hz => ((Real.rpow_pos_of_pos hs b).ne' hz).elim
  · have ht : Tendsto (fun s : ℝ => s ^ (a - b)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (sub_pos.mpr h).ne'] using
        ((Real.continuous_rpow_const (sub_pos.mpr h).le).tendsto 0).mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Real.rpow_sub hs a b

theorem eq_zero_of_isLittleO_pow_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (q : ℕ) (a : F)
    (h : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s : ℝ => (s ^ q) • a) (fun s : ℝ => s ^ q)) : a = 0 := by
  have heq : (fun s : ℝ => (s ^ q)⁻¹ • ((s ^ q) • a)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => a) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero q (ne_of_gt (show 0 < s from hs))), one_smul]
  exact tendsto_nhds_unique tendsto_const_nhds
    (h.tendsto_inv_smul_nhds_zero.congr' heq)

theorem taylorCoefficient_eq_zero_of_lt_growth {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (A : ℕ → F) {a : ℝ}
    (hbound : IsBigO (𝓝[>] (0 : ℝ)) f (fun s : ℝ => s ^ a))
    (hexp : ∀ q : ℕ, 0 < q → IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => f s - ∑ i ∈ Finset.range q, s ^ (i + 1) • A (i + 1))
      (fun s : ℝ => s ^ q)) :
    ∀ j : ℕ, 0 < j → (j : ℝ) < a → A j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hja
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hpoly (s : ℝ) : (∑ i ∈ Finset.range (q + 1), s ^ (i + 1) • A (i + 1)) =
        s ^ (q + 1) • A (q + 1) := by
      rw [Finset.sum_range_succ]
      have hz : (∑ i ∈ Finset.range q, s ^ (i + 1) • A (i + 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hiq : i + 1 < q + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hi)
        rw [ih (i + 1) hiq (Nat.succ_pos _) ((Nat.cast_lt.mpr hiq).trans hja), smul_zero]
      rw [hz, zero_add]
    have hf : IsLittleO (𝓝[>] (0 : ℝ)) f (fun s : ℝ => s ^ (q + 1)) := by
      simpa only [Real.rpow_natCast] using hbound.trans_isLittleO (isLittleO_rpow_nhdsGT_zero hja)
    have hdiff := hf.sub (hexp (q + 1) (Nat.succ_pos _))
    apply eq_zero_of_isLittleO_pow_smul (q + 1) (A (q + 1))
    convert hdiff using 1
    funext s
    rw [hpoly]
    abel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_coherent_taylor_coefficients_of_finite_jets (f : ℝ → F)
    (h : ∀ q : ℕ, 0 < q → ∃ A : ℕ → F, ∀ j : ℕ, 0 < j → j ≤ q →
      IsLittleO (𝓝[>] (0 : ℝ))
        (fun s => f s - ∑ i ∈ Finset.range j, s ^ (i + 1) • A (i + 1))
        (fun s : ℝ => s ^ j)) :
    ∃ A : ℕ → F, ∀ q : ℕ, 0 < q →
      IsLittleO (𝓝[>] (0 : ℝ))
        (fun s => f s - ∑ i ∈ Finset.range q, s ^ (i + 1) • A (i + 1))
        (fun s : ℝ => s ^ q) := by
  classical
  choose A hA using fun q : ℕ => h (q + 1) (Nat.succ_pos _)
  have agree : ∀ j : ℕ, 0 < j → ∀ p q : ℕ, j ≤ p + 1 → j ≤ q + 1 → A p j = A q j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj p q hjp hjq
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      have hprev (s : ℝ) : (∑ i ∈ Finset.range k, s ^ (i + 1) • A p (i + 1)) =
          ∑ i ∈ Finset.range k, s ^ (i + 1) • A q (i + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i + 1 < k + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hi)
        rw [ih (i + 1) hik (Nat.succ_pos _) p q (by omega) (by omega)]
      have hdiff := (hA q (k + 1) (Nat.succ_pos _) hjq).sub
        (hA p (k + 1) (Nat.succ_pos _) hjp)
      have hz : A p (k + 1) - A q (k + 1) = 0 := by
        apply eq_zero_of_isLittleO_pow_smul (k + 1)
        convert hdiff using 1
        funext s
        rw [Finset.sum_range_succ, Finset.sum_range_succ, hprev, smul_sub]
        abel
      exact sub_eq_zero.mp hz
  refine ⟨fun j => A j j, ?_⟩
  intro q hq
  have heq (s : ℝ) : (∑ i ∈ Finset.range q, s ^ (i + 1) • A (i + 1) (i + 1)) =
      ∑ i ∈ Finset.range q, s ^ (i + 1) • A q (i + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [agree (i + 1) (Nat.succ_pos _) (i + 1) q (by omega) (by have := Finset.mem_range.mp hi; omega)]
  simpa only [heq] using hA q q hq (Nat.le_succ q)


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
