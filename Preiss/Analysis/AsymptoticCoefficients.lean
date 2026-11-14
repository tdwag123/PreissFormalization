module
public import Mathlib.Analysis.Asymptotics.Lemmas
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

end Preiss
