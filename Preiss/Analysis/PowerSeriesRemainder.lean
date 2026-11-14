module
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
open Filter Finset
open scoped BigOperators Topology
namespace Preiss

theorem summable_pow_mul_halfPower_div_factorial (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun k : ℕ => a^k * (k : ℝ)^((k : ℝ)/2) / (k.factorial : ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ((2*a*Real.exp 1)^2 + 1)
  apply (summable_geometric_of_norm_lt_one (x := (1/2 : ℝ)) (by norm_num)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkR : (2*a*Real.exp 1)^2 + 1 ≤ (k : ℝ) := hN.trans (by exact_mod_cast hk)
  have hkpos : 0 < (k : ℝ) := by nlinarith [sq_nonneg (2*a*Real.exp 1)]
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hlarge : 2*a*Real.exp 1 ≤ Real.sqrt (k : ℝ) := by
    apply (Real.le_sqrt (by positivity) hkpos.le).mpr
    linarith
  have hratio : a*Real.exp 1 / Real.sqrt (k : ℝ) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hsqrt).mpr
    linarith
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_div_two_eq_sqrt _ hkpos.le,
    Real.rpow_natCast]
  have heq : a^k * Real.sqrt (k : ℝ)^k / (k.factorial : ℝ) =
      (a / Real.sqrt (k : ℝ))^k * ((k : ℝ)^k / (k.factorial : ℝ)) := by
    have hkpow : (k : ℝ)^k = Real.sqrt (k : ℝ)^k * Real.sqrt (k : ℝ)^k := by
      rw [← mul_pow, Real.mul_self_sqrt hkpos.le]
    rw [hkpow, div_pow]
    field_simp [hsqrt.ne']
  rw [heq]
  calc
    _ ≤ (a / Real.sqrt (k : ℝ))^k * Real.exp (k : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k) (by positivity)
    _ = (a*Real.exp 1 / Real.sqrt (k : ℝ))^k := by
      rw [show Real.exp (k : ℝ) = (Real.exp 1)^k by simpa using Real.exp_nat_mul 1 k,
        ← mul_pow]
      congr 1
      ring
    _ ≤ (1/2 : ℝ)^k := pow_le_pow_left₀ (by positivity) hratio k

theorem abs_power_series_tail_le {f c : ℕ → ℝ} {r A : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hc : ∀ k, 0 ≤ c k) (hcs : Summable c)
    (hf : HasSum f A) (hb : ∀ k, |f k| ≤ c k * r^k) (N : ℕ) :
    |A - ∑ k ∈ range N, f k| ≤ (∑' k, c k) * r^N := by
  have ht : HasSum (fun k => f (k+N)) (A - ∑ k ∈ range N, f k) :=
    (hasSum_nat_add_iff' N).mpr hf
  have hct : Summable (fun k => c (k+N)) := (summable_nat_add_iff N).mpr hcs
  have htail : |∑' k, f (k+N)| ≤ (∑' k, c (k+N)) * r^N := by
    rw [← Real.norm_eq_abs]
    apply tsum_of_norm_bounded (hct.hasSum.mul_right (r^N))
    intro k
    rw [Real.norm_eq_abs]
    exact (hb (k+N)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hr hr1 (Nat.le_add_left N k)) (hc _))
  have htotal : (∑' k, c (k+N)) ≤ ∑' k, c k := by
    have heq := hcs.sum_add_tsum_nat_add N
    have hn : 0 ≤ ∑ k ∈ range N, c k := sum_nonneg (fun k _ => hc k)
    linarith
  rw [← ht.tsum_eq]
  exact htail.trans (mul_le_mul_of_nonneg_right htotal (pow_nonneg hr _))

theorem abs_sum_positive_powers_le {f c : ℕ → ℝ} {e : ℕ → ℕ} {r : ℝ}
    (hr : 1 ≤ r) (hc : ∀ k, 0 ≤ c k) (hcs : Summable c)
    (hb : ∀ k, 0 < k → |f k| ≤ c k * r^(e k)) (q N : ℕ)
    (he : ∀ k ∈ range q, e (k+1) ≤ N) :
    |∑ k ∈ range q, f (k+1)| ≤ (∑' k, c k) * r^N := by
  have hcoeff : (∑ k ∈ range q, c (k+1)) ≤ ∑' k, c k := by
    have h := hcs.sum_le_tsum (range (q+1)) (fun k _ => hc k)
    rw [sum_range_succ'] at h
    linarith [hc 0]
  calc
    _ ≤ ∑ k ∈ range q, |f (k+1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range q, c (k+1) * r^N := by
      apply sum_le_sum
      intro k hk
      exact (hb (k+1) (Nat.succ_pos k)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hr (he k hk)) (hc _))
    _ = (∑ k ∈ range q, c (k+1)) * r^N := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (zero_le_one.trans hr) _)

theorem power_series_gaussian_taylor_remainder {f c : ℕ → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hc : ∀ k, 0 ≤ c k) (hcs : Summable c)
    (hf : HasSum f (Real.exp (r^2))) (hf0 : f 0 = 1)
    (hb : ∀ k, |f k| ≤ c k * r^k) (q : ℕ) :
    |(∑ k ∈ range (2*q), f (k+1)) -
      ∑ j ∈ range q, r^(2*(j+1)) / ((j+1).factorial : ℝ)| ≤
      ((∑' k, c k) + Real.exp 1) * r^(2*q+1) := by
  let d (j : ℕ) : ℝ := 1 / (j.factorial : ℝ)
  have hd (j : ℕ) : 0 ≤ d j := by dsimp [d]; positivity
  have hds : HasSum d (Real.exp 1) := by
    simpa only [d,one_pow,Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  have hg : HasSum (fun j : ℕ => (r^2)^j / (j.factorial : ℝ)) (Real.exp (r^2)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (r^2)
  have hgBound (j : ℕ) : |(r^2)^j / (j.factorial : ℝ)| ≤ d j * (r^2)^j := by
    rw [abs_of_nonneg (by positivity)]
    dsimp [d]
    exact le_of_eq (by ring)
  by_cases hr1 : r ≤ 1
  · have hfTail := abs_power_series_tail_le hr hr1 hc hcs hf hb (2*q+1)
    have hgTail := abs_power_series_tail_le (sq_nonneg r)
      (by nlinarith : r^2 ≤ 1) hd hds.summable hg hgBound (q+1)
    rw [hds.tsum_eq] at hgTail
    rw [sum_range_succ',hf0] at hfTail
    rw [sum_range_succ'] at hgTail
    simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at hgTail
    have hp : (r^2)^(q+1) ≤ r^(2*q+1) := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one hr hr1 (by omega)
    calc
      _ = |((∑ k ∈ range (2*q),f (k+1)) + 1 - Real.exp (r^2)) +
          (Real.exp (r^2) - (1 + ∑ j ∈ range q,(r^2)^(j+1)/((j+1).factorial : ℝ)))| := by
        simp only [pow_mul]
        congr 1
        ring
      _ ≤ |(∑ k ∈ range (2*q),f (k+1)) + 1 - Real.exp (r^2)| +
          |Real.exp (r^2) - (1 + ∑ j ∈ range q,(r^2)^(j+1)/((j+1).factorial : ℝ))| := abs_add_le _ _
      _ ≤ (∑' k,c k)*r^(2*q+1) + Real.exp 1*(r^2)^(q+1) := by
        apply add_le_add
        · simpa only [abs_sub_comm, add_comm] using hfTail
        · simpa only [add_comm] using hgTail
      _ ≤ (∑' k,c k)*r^(2*q+1) + Real.exp 1*r^(2*q+1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (Real.exp_pos 1).le)
      _ = _ := by ring
  · have hrlarge : 1 ≤ r := (lt_of_not_ge hr1).le
    have hF := abs_sum_positive_powers_le (e := id) hrlarge hc hcs
      (fun k _ => hb k) (2*q) (2*q+1) (fun k hk => by simp only [id_eq]; have := mem_range.mp hk; omega)
    have hG := abs_sum_positive_powers_le (f := fun j => r^(2*j)/(j.factorial : ℝ))
      (e := fun j => 2*j) hrlarge hd hds.summable
      (fun j _ => by rw [abs_of_nonneg (by positivity)]; dsimp [d]; exact le_of_eq (by ring))
      q (2*q+1) (fun j hj => by have := mem_range.mp hj; omega)
    rw [hds.tsum_eq] at hG
    exact (abs_sub _ _).trans ((add_le_add hF hG).trans_eq (by ring))


end Preiss
