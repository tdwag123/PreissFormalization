module
public import Preiss.Geometry.Euclidean
public import Preiss.Analysis.AnnulusIntegrability
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace Preiss
variable {n : ℕ}

def HasPolynomialGrowthBound (μ : Measure (Euclidean n)) (C p : ℝ) : Prop :=
  0 ≤ C ∧ 0 ≤ p ∧ ∀ R > 0,
    μ (closedBall 0 R) ≤ ENNReal.ofReal (C * (1 + R) ^ p)

theorem summable_gaussian_annulus_majorant (C p : ℝ) (hC : 0 ≤ C)
    (d : ℕ) (s : ℝ) (hs : 0 < s) :
    Summable (fun j : ℕ =>
      (((j : ℝ) + 1) ^ d * Real.exp (-s * (j : ℝ) ^ 2)) *
        (C * ((j : ℝ) + 2) ^ p)) := by
  let r := Real.exp (-s)
  let K := d + ⌈p⌉₊
  have hrpos : 0 < r := Real.exp_pos _
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg hrpos.le]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)
  have hsum : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ K * r ^ j) := by
    have hbase : Summable (fun j : ℕ => (j : ℝ) ^ K * r ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) K (r := r) hr
    have hshift : Summable (fun j : ℕ => ((j + 2 : ℕ) : ℝ) ^ K * r ^ (j + 2)) :=
      (summable_nat_add_iff 2).mpr hbase
    have hscaled := hshift.mul_right ((r ^ 2)⁻¹)
    simpa [Nat.cast_add, Nat.cast_ofNat, pow_add, mul_assoc, ne_of_gt hrpos] using hscaled
  apply (hsum.mul_left C).of_nonneg_of_le
  · intro j
    positivity
  · intro j
    have hpow : ((j : ℝ) + 1) ^ d * ((j : ℝ) + 2) ^ p ≤ ((j : ℝ) + 2) ^ K := by
      dsimp [K]
      rw [pow_add]
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (by linarith) d
      · rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) j; linarith) (Nat.le_ceil p)
      · positivity
      · positivity
    have hj : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
      exact_mod_cast (show j ≤ j ^ 2 by simpa only [pow_two] using Nat.le_mul_self j)
    have hexp : Real.exp (-s * (j : ℝ) ^ 2) ≤ r ^ j := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ = C * (((j : ℝ) + 1) ^ d * ((j : ℝ) + 2) ^ p) *
          Real.exp (-s * (j : ℝ) ^ 2) := by ring
      _ ≤ C * ((j : ℝ) + 2) ^ K * r ^ j :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring

theorem integrable_norm_pow_mul_gaussian_of_ball_bound {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ R > 0, μ (closedBall 0 R) ≤ ENNReal.ofReal (C * (1 + R) ^ p))
    (d : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2)) μ := by
  have hfinite : ∀ R > 0, μ (closedBall 0 R) < ∞ :=
    fun R hR => (hgrowth R hR).trans_lt ENNReal.ofReal_lt_top
  have hbound (j : ℕ) (z : Euclidean n) (hj : (j : ℝ) ≤ ‖z‖)
      (hj' : ‖z‖ ≤ (j : ℝ) + 1) :
      ‖‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2)‖ ≤
        ((j : ℝ) + 1) ^ d * Real.exp (-s * (j : ℝ) ^ 2) := by
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (norm_nonneg z) hj' d
    · apply Real.exp_le_exp.mpr
      have hsq : (j : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hj 2
      nlinarith
    · positivity
    · positivity
  have hmass (j : ℕ) : μ.real (closedBall 0 ((j : ℝ) + 1)) ≤
      C * ((j : ℝ) + 2) ^ p := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgrowth ((j : ℝ) + 1) (by positivity))
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    convert h using 1 <;> congr 2 <;> ring
  apply integrable_of_summable_annulus_bounds μ hfinite _ (by fun_prop)
    (fun j => ((j : ℝ) + 1) ^ d * Real.exp (-s * (j : ℝ) ^ 2)) (by intro j; positivity) hbound
  apply (summable_gaussian_annulus_majorant C p hC d s hs).of_nonneg_of_le
  · intro j
    positivity
  · intro j
    exact mul_le_mul_of_nonneg_left (hmass j) (by positivity)

theorem gaussian_annulus_integral_bound {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ R > 0, μ (closedBall 0 R) ≤ ENNReal.ofReal (C * (1 + R) ^ p))
    (d : ℕ) (s : ℝ) (hs : 0 < s) (j : ℕ) :
    (∫ z in {z : Euclidean n | (j : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ (j : ℝ) + 1},
      ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2) ∂μ) ≤
      (((j : ℝ) + 1) ^ d * Real.exp (-s * (j : ℝ) ^ 2)) *
        (C * ((j : ℝ) + 2) ^ p) := by
  let S := {z : Euclidean n | (j : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ (j : ℝ) + 1}
  have hsub : S ⊆ closedBall 0 ((j : ℝ) + 1) := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hz.2
  have hmass := hgrowth ((j : ℝ) + 1) (by positivity)
  have hfinite : μ (closedBall 0 ((j : ℝ) + 1)) < ∞ :=
    hmass.trans_lt ENNReal.ofReal_lt_top
  have hfiniteS : μ S < ∞ := (measure_mono hsub).trans_lt hfinite
  have hb : ∀ z ∈ S, ‖‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2)‖ ≤
      ((j : ℝ) + 1) ^ d * Real.exp (-s * (j : ℝ) ^ 2) := by
    intro z hz
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (norm_nonneg z) hz.2 d
    · apply Real.exp_le_exp.mpr
      have hsq := pow_le_pow_left₀ (show 0 ≤ (j : ℝ) by positivity) hz.1 2
      nlinarith
    · positivity
    · positivity
  have hlocal := norm_setIntegral_le_of_norm_le_const hfiniteS hb
  rw [Real.norm_of_nonneg (integral_nonneg (fun z => by positivity))] at hlocal
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hmass)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  convert h using 1 <;> congr 2 <;> ring

theorem gaussian_tail_le_annulus_sum {n : ℕ}
    (μ : Measure (Euclidean n)) (C p : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ R > 0, μ (closedBall 0 R) ≤ ENNReal.ofReal (C * (1 + R) ^ p))
    (d : ℕ) (s : ℝ) (hs : 0 < s) (N : ℕ) (R : ℝ) (hR : (N : ℝ) ≤ R) :
    (∫ z in (closedBall 0 R)ᶜ, ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2) ∂μ) ≤
      ∑' j : ℕ, ((((j + N : ℕ) : ℝ) + 1) ^ d *
        Real.exp (-s * ((j + N : ℕ) : ℝ) ^ 2)) *
          (C * (((j + N : ℕ) : ℝ) + 2) ^ p) := by
  let f : Euclidean n → ℝ := fun z => ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2)
  let S : ℕ → Set (Euclidean n) := fun j =>
    {z | ((j + N : ℕ) : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ ((j + N : ℕ) : ℝ) + 1}
  have hf : Integrable f μ :=
    integrable_norm_pow_mul_gaussian_of_ball_bound μ C p hC hgrowth d s hs
  have hpos : ∀ z, 0 ≤ f z := by intro z; dsimp [f]; positivity
  have hcover : (closedBall (0 : Euclidean n) R)ᶜ ⊆ ⋃ j, S j := by
    intro z hz
    have hzR : R < ‖z‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
    have hfloor : N ≤ ⌊‖z‖⌋₊ := (Nat.le_floor_iff (norm_nonneg z)).mpr (hR.trans hzR.le)
    refine mem_iUnion.mpr ⟨⌊‖z‖⌋₊ - N, ?_⟩
    dsimp [S]
    rw [Nat.sub_add_cancel hfloor]
    exact ⟨Nat.floor_le (norm_nonneg z), (Nat.lt_floor_add_one ‖z‖).le⟩
  apply (setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall hpos)
    (Filter.Eventually.of_forall hcover)).trans
  apply integral_iUnion_le_tsum_bounds μ f hf hpos S
  · intro j
    exact ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet
  · exact (summable_nat_add_iff N).mpr (summable_gaussian_annulus_majorant C p hC d s hs)
  · intro j
    exact gaussian_annulus_integral_bound μ C p hC hgrowth d s hs (j + N)

theorem exists_uniform_gaussian_tail_radius {n : ℕ}
    (C p : ℝ) (hC : 0 ≤ C) (d : ℕ) (s : ℝ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ (μ : Measure (Euclidean n)),
      (∀ R > 0, μ (closedBall 0 R) ≤ ENNReal.ofReal (C * (1 + R) ^ p)) →
      ∀ R ≥ R₀,
      (∫ z in (closedBall 0 R)ᶜ, ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2) ∂μ) < ε := by
  let B : ℕ → ℝ := fun j =>
    (((j : ℝ) + 1) ^ d * Real.exp (-s * (j : ℝ) ^ 2)) *
      (C * ((j : ℝ) + 2) ^ p)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_sum_nat_add B).eventually (gt_mem_nhds hε))
  refine ⟨(N : ℝ) + 1, by positivity, ?_⟩
  intro μ hμ R hR
  have hNR : (N : ℝ) ≤ R := by linarith
  exact (gaussian_tail_le_annulus_sum μ C p hC hμ d s hs N R hNR).trans_lt (hN N le_rfl)

theorem integrable_norm_pow_mul_gaussian_of_polynomial_growth
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (C p : ℝ)
    (hgrowth : HasPolynomialGrowthBound μ C p) (d : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun z => ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2)) μ := by
  exact integrable_norm_pow_mul_gaussian_of_ball_bound μ C p hgrowth.1 hgrowth.2.2 d s hs

theorem gaussian_polynomial_uniform_tail (C p : ℝ) (d : ℕ) (s : ℝ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ (μ : Measure (Euclidean n)), μ.Regular →
      HasPolynomialGrowthBound μ C p → ∀ R ≥ R₀,
      (∫ z in (closedBall 0 R)ᶜ, ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2) ∂μ) < ε := by
  by_cases hC : 0 ≤ C
  · obtain ⟨R₀, hR₀, htail⟩ := exists_uniform_gaussian_tail_radius (n := n) C p hC d s hs ε hε
    exact ⟨R₀, hR₀, fun μ _ hgrowth R hR => htail μ hgrowth.2.2 R hR⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro μ hμ hgrowth
    exact (hC hgrowth.1).elim

theorem hasDerivAt_integral_polynomial_mul_gaussian
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (C p : ℝ)
    (hgrowth : HasPolynomialGrowthBound μ C p)
    (P : MvPolynomial (Fin n) ℝ) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => ∫ z, MvPolynomial.eval (fun j => z j) P *
      Real.exp (-t * ‖z‖ ^ 2) ∂μ)
      (-(∫ z, ‖z‖ ^ 2 * MvPolynomial.eval (fun j => z j) P *
        Real.exp (-s * ‖z‖ ^ 2) ∂μ)) s := by
  sorry

end Preiss
