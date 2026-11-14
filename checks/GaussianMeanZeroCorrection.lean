module
public import Preiss.Analysis.GaussianBilinearVectorTrace
public import Mathlib.Tactic

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace Preiss

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
#print axioms Preiss.gaussian_integral_bilinear_eq_trace_of_mean_zero_correction
