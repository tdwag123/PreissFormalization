import Preiss.Analysis.GaussianBilinearNorm
import Preiss.Analysis.GaussianQuadraticLowerBound
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
namespace Preiss
theorem gaussian_quadratic_bounds_of_mean_square_identity
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ u v, A u v = A v u)
    (ω : E →L[ℝ] E →L[ℝ] F) (hd : 0 < Module.finrank ℝ E)
    (q : ℝ) (hq : 0 ≤ q)
    (hpoint : ∀ v, (A v v)^2 ≤ q * ‖ω v v‖^2)
    (hmean : (∫ v, ‖ω v v‖^2 ∂stdGaussian E) =
      -8*(∫ v, A v v ∂stdGaussian E)) :
    (∫ v, (A v v)^2 ∂stdGaussian E) ≤ -8*q*(∫ v, A v v ∂stdGaussian E) ∧
    -8*(Module.finrank ℝ E : ℝ)*q/((Module.finrank ℝ E : ℝ)+2) ≤
      ∫ v, A v v ∂stdGaussian E := by
  have hAint : Integrable (fun v => (A v v)^2) (stdGaussian E) := by
    simpa only [Real.norm_eq_abs, sq_abs] using integrable_gaussian_norm_sq_bilinear A
  have hωint := (integrable_gaussian_norm_sq_bilinear ω).const_mul q
  have h := integral_mono_ae hAint hωint (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul, hmean] at h
  have hupper : (∫ v, (A v v)^2 ∂stdGaussian E) ≤
      -8*q*(∫ v, A v v ∂stdGaussian E) := by nlinarith [h]
  exact ⟨hupper, gaussian_bilinear_integral_lower_bound_of_square_upper A hA hd q hq hupper⟩
end Preiss
#print axioms Preiss.gaussian_quadratic_bounds_of_mean_square_identity
