import Preiss.Analysis.GaussianGrowth
import Preiss.Analysis.PolynomialNormBound
import Preiss.Analysis.Vague.UniformTails

/-! # Gaussian polynomial tests under vague convergence

Uniform Gaussian tail bounds extend vague convergence from compactly supported tests
to polynomial multiples of a Gaussian.
-/

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace Preiss
variable {n : ℕ}

theorem polynomial_gaussian_uniform_norm_tail
    (C p : ℝ) (P : MvPolynomial (Fin n) ℝ) (s : ℝ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ (μ : Measure (Euclidean n)), μ.Regular →
      HasPolynomialGrowthBound μ C p → ∀ R ≥ R₀,
      (∫ z in (closedBall 0 R)ᶜ,
        ‖MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖ ^ 2)‖ ∂μ) < ε := by
  obtain ⟨D, hD, d, hd⟩ := exists_polynomial_norm_bound_outside_unit_ball P
  have hDp : 0 < D + 1 := by positivity
  obtain ⟨R₀, hR₀, htail⟩ := gaussian_polynomial_uniform_tail (n := n)
    C p d s hs (ε / (D + 1)) (by positivity)
  refine ⟨max R₀ 1, lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro μ hμ hgrowth R hR
  have hRtail : R₀ ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := (le_max_right _ _).trans hR
  have hpoly : Integrable (fun z : Euclidean n =>
      MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖ ^ 2)) μ := by
    simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_polynomial_mul_gaussian
      μ C p hgrowth.1 hgrowth.2.2 P 0 s hs
  have hgauss := integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ C p hgrowth d s hs
  have hbound : (∫ z in (closedBall 0 R)ᶜ,
      ‖MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖ ^ 2)‖ ∂μ) ≤
      D * (∫ z in (closedBall 0 R)ᶜ, ‖z‖ ^ d * Real.exp (-s * ‖z‖ ^ 2) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hpoly.norm.integrableOn (hgauss.const_mul D).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with z hz
    have hzR : R < ‖z‖ := by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hd z (hRone.trans hzR.le)) (Real.exp_pos _).le
  have hsmall := htail μ hμ hgrowth R hRtail
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_left hsmall.le hD)
  have hid : (D + 1) * (ε / (D + 1)) = ε := mul_div_cancel₀ ε hDp.ne'
  have hδ : 0 < ε / (D + 1) := by positivity
  nlinarith

theorem vague_integral_polynomial_mul_gaussian
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) (C p : ℝ)
    (hgrowth : ∀ i, HasPolynomialGrowthBound (μ i) C p)
    (hνgrowth : HasPolynomialGrowthBound ν C p)
    (P : MvPolynomial (Fin n) ℝ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun i => ∫ z, MvPolynomial.eval (fun j => z j) P *
      Real.exp (-s * ‖z‖ ^ 2) ∂μ i) atTop
      (𝓝 (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖ ^ 2) ∂ν)) := by
  have hc : Continuous (fun z : Euclidean n => MvPolynomial.eval (fun j => z j) P) :=
    P.continuous_eval.comp (by fun_prop)
  apply vague_integral_of_uniform_norm_tails μ ν hμ hν hlim _ (by fun_prop)
  · intro i
    simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_polynomial_mul_gaussian
      (μ i) C p (hgrowth i).1 (hgrowth i).2.2 P 0 s hs
  · simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_polynomial_mul_gaussian
      ν C p hνgrowth.1 hνgrowth.2.2 P 0 s hs
  · intro ε hε
    obtain ⟨R, hR, htail⟩ := polynomial_gaussian_uniform_norm_tail C p P s hs ε hε
    exact ⟨closedBall 0 R, isCompact_closedBall _ _,
      fun i => htail (μ i) (hμ i) (hgrowth i) R le_rfl,
      htail ν hν hνgrowth R le_rfl⟩

end Preiss
