import Preiss.Analysis.BilinearIntegralLimits
import Preiss.Analysis.GaussianBilinearNorm
import Mathlib.Tactic

open MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators
namespace Preiss

theorem gaussian_bilinear_contraction_of_weighted_moment_limits
    {X I E F ι κ : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ F)
    (μ : Measure X) (l : Filter I) [l.NeBot]
    (weight : I → X → ℝ) (scale : I → ℝ) (p : X → E) (q : X → F)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (ω : E →L[ℝ] E →L[ℝ] F)
    (hsymm : ∀ u v, ω u v = ω v u)
    (hmean : (∫ v, ω v v ∂stdGaussian E) = 0)
    (hint₂ : ∀ i j, ∀ᶠ t in l,
      Integrable (fun x => weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x))) μ)
    (hlim₂ : ∀ i j, Tendsto (fun t => scale t * ∫ x,
      weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x)) ∂μ)
      l (𝓝 (inner ℝ (e i) (e j) / 2)))
    (hint₃ : ∀ i j, ∀ᶠ t in l,
      Integrable (fun x => weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x) *
        inner ℝ (ω (e i) (e j)) (q x))) μ)
    (hlim₃ : ∀ i j, Tendsto (fun t => scale t * ∫ x,
      weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x) *
        inner ℝ (ω (e i) (e j)) (q x)) ∂μ) l (𝓝 (‖ω (e i) (e j)‖^2 / 8)))
    (hzero : Tendsto (fun t => scale t * ∫ x, weight t x *
      (A (p x) (p x) + inner ℝ (ω (p x) (p x)) (q x)) ∂μ) l (𝓝 0)) :
    (∫ v, ‖ω v v‖^2 ∂stdGaussian E) = -8 * ∫ v, A v v ∂stdGaussian E := by
  classical
  let Q (ij : ι × ι) (x : X) := inner ℝ (e ij.1) (p x) * inner ℝ (e ij.2) (p x)
  let a (ij : ι × ι) := A (e ij.1) (e ij.2)
  let L (ij : ι × ι) := inner ℝ (e ij.1) (e ij.2) / 2
  have hquad := tendsto_weighted_integral_finite_linear_combination μ l weight scale Q a L
    (fun ij => hint₂ ij.1 ij.2) (fun ij => hlim₂ ij.1 ij.2)
  have hQ (x : X) : (∑ ij : ι × ι, a ij * Q ij x) = A (p x) (p x) := by
    dsimp only [a, Q]
    rw [Fintype.sum_prod_type, bilinear_diagonal_eq_sum_orthonormalBasis e A (p x)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_eq_mul]
    ring
  simp_rw [hQ] at hquad
  have hL : (∑ ij : ι × ι, a ij * L ij) = bilinearTrace A / 2 := by
    rw [bilinearTrace_eq_sum_diagonal A e]
    simp [a, L, Fintype.sum_prod_type, e.inner_eq_ite, Finset.sum_div, ite_div, mul_ite, div_eq_mul_inv, Finset.sum_mul]
  rw [hL] at hquad
  let T (ij : ι × ι) (x : X) := Q ij x * inner ℝ (ω (e ij.1) (e ij.2)) (q x)
  let N (ij : ι × ι) := ‖ω (e ij.1) (e ij.2)‖^2 / 8
  have hmixed := tendsto_weighted_integral_finite_linear_combination μ l weight scale T
    (fun _ => 1) N (fun ij => hint₃ ij.1 ij.2) (fun ij => hlim₃ ij.1 ij.2)
  have hT (x : X) : (∑ ij : ι × ι, (1 : ℝ) * T ij x) =
      inner ℝ (ω (p x) (p x)) (q x) := by
    dsimp only [T, Q]
    rw [Fintype.sum_prod_type, bilinear_diagonal_eq_sum_orthonormalBasis e ω (p x)]
    simp only [one_mul, sum_inner, real_inner_smul_left]
  simp_rw [hT] at hmixed
  have hN : (∑ ij : ι × ι, (1 : ℝ) * N ij) =
      (∑ i, ∑ j, ‖ω (e i) (e j)‖^2) / 8 := by
    simp only [N, one_mul, Fintype.sum_prod_type, Finset.sum_div]
  rw [hN] at hmixed
  have htotal : Tendsto (fun t => scale t * ∫ x, weight t x *
      (A (p x) (p x) + inner ℝ (ω (p x) (p x)) (q x)) ∂μ)
      l (𝓝 (bilinearTrace A / 2 + (∑ i, ∑ j, ‖ω (e i) (e j)‖^2) / 8)) := by
    apply (hquad.2.add hmixed.2).congr'
    filter_upwards [hquad.1, hmixed.1] with t htA htω
    have hsum : (fun x => weight t x * (A (p x) (p x) + inner ℝ (ω (p x) (p x)) (q x))) =
        (fun x => weight t x * A (p x) (p x) + weight t x * inner ℝ (ω (p x) (p x)) (q x)) := by
      funext x
      ring
    rw [hsum, integral_add htA htω]
    ring
  have heq := tendsto_nhds_unique hzero htotal
  rw [gaussian_integral_norm_sq_bilinear_of_mean_zero e f ω hsymm hmean,
    gaussian_integral_bilinear_eq_trace]
  nlinarith

end Preiss

#print axioms Preiss.gaussian_bilinear_contraction_of_weighted_moment_limits
