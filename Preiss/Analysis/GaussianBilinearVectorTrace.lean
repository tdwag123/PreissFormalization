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

theorem gaussian_integral_bilinear_eq_trace_of_mean_zero_correction
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D A : E →L[ℝ] E →L[ℝ] ℝ) (Ω : E →L[ℝ] E →L[ℝ] F)
    (hmean : (∫ v, Ω v v ∂stdGaussian E) = 0) (b : F)
    (hA : ∀ u v, A u v = D u v + inner ℝ (Ω u v) b) :
    bilinearTrace D = ∫ v, A v v ∂stdGaussian E := by
  have hinner : Integrable (fun u => inner ℝ (Ω u u) b) (stdGaussian E) := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
      (innerSL ℝ b).integrable_comp (integrable_gaussian_bilinear_diagonal Ω)
  have hz := gaussian_integral_inner_bilinear_eq_zero_of_mean_zero Ω hmean b
  calc
    bilinearTrace D = ∫ u, D u u ∂stdGaussian E :=
      (gaussian_integral_bilinear_eq_trace D).symm
    _ = (∫ u, D u u ∂stdGaussian E) + ∫ u, inner ℝ (Ω u u) b ∂stdGaussian E := by
      rw [hz, add_zero]
    _ = ∫ u, D u u + inner ℝ (Ω u u) b ∂stdGaussian E :=
      (integral_add (integrable_gaussian_bilinear_diagonal D) hinner).symm
    _ = ∫ u, A u u ∂stdGaussian E := by simp_rw [hA]


end Preiss
