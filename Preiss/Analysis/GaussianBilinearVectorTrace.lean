module
public import Preiss.Analysis.GaussianQuadraticForms
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Preiss

theorem gaussian_integral_bilinear_eq_basis_sum
    {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E →L[ℝ] F) :
    (∫ v, A v v ∂stdGaussian E) = ∑ i, A (e i) (e i) := by
  apply ext_inner_left ℝ
  intro w
  let L : F →L[ℝ] ℝ := innerSL ℝ w
  let B : E →L[ℝ] E →L[ℝ] ℝ := ((ContinuousLinearMap.compL ℝ E F ℝ) L).comp A
  change L (∫ v, A v v ∂stdGaussian E) = L (∑ i, A (e i) (e i))
  rw [← L.integral_comp_comm (integrable_gaussian_bilinear_diagonal A), map_sum]
  change (∫ v, B v v ∂stdGaussian E) = ∑ i, B (e i) (e i)
  rw [gaussian_integral_bilinear_eq_trace, bilinearTrace_eq_sum_diagonal B e]


theorem gaussian_integral_inner_bilinear_eq_zero_of_mean_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] E →L[ℝ] F)
    (hmean : (∫ v, A v v ∂stdGaussian E) = 0) (w : F) :
    (∫ v, inner ℝ (A v v) w ∂stdGaussian E) = 0 := by
  have h := (innerSL ℝ w).integral_comp_comm (integrable_gaussian_bilinear_diagonal A)
  rw [hmean] at h
  simpa only [innerSL_apply_apply, map_zero, real_inner_comm] using h

theorem gaussian_integral_inner_sq_mul_bilinear_of_mean_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] E →L[ℝ] F)
    (hmean : (∫ v, A v v ∂stdGaussian E) = 0) (y : E) (w : F) :
    (∫ v, (inner ℝ y v)^2 * inner ℝ (A v v) w ∂stdGaussian E) =
      2 * inner ℝ (A y y) w := by
  let D : E →L[ℝ] E →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ E F ℝ) (innerSL ℝ w)).comp A
  have hD (u v : E) : D u v = inner ℝ (A u v) w := real_inner_comm _ _
  have hz : bilinearTrace D = 0 := by
    rw [← gaussian_integral_bilinear_eq_trace D]
    simp_rw [hD]
    exact gaussian_integral_inner_bilinear_eq_zero_of_mean_zero A hmean w
  simpa only [hD, hz, mul_zero, zero_add] using gaussian_integral_inner_sq_mul_bilinear D y

end Preiss
