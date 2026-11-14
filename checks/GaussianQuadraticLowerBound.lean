import Preiss.Analysis.GaussianQuadraticForms
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
namespace Preiss
theorem quadratic_lower_bound_of_square_upper
    (d q t : ℝ) (hd : 0 < d) (hq : 0 ≤ q)
    (h : (1+2/d)*t^2 ≤ -8*q*t) :
    -8*d*q/(d+2) ≤ t := by
  apply (div_le_iff₀ (by linarith : 0 < d+2)).mpr
  have hmul := mul_le_mul_of_nonneg_left h hd.le
  have hfac : d*(1+2/d)=d+2 := by field_simp; ring
  rw [← mul_assoc, hfac] at hmul
  have hquad : (d+2)*t^2 ≤ -8*d*q*t := by nlinarith [hmul]
  by_contra hn
  have ht : t*(d+2) < -8*d*q := lt_of_not_ge hn
  have ht0 : t < 0 := by nlinarith
  have hp : 0 < t*(t*(d+2)+8*d*q) := mul_pos_of_neg_of_neg ht0 (by linarith)
  nlinarith

theorem gaussian_bilinear_integral_lower_bound_of_square_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u v, A u v = A v u)
    (hd : 0 < Module.finrank ℝ E) (q : ℝ) (hq : 0 ≤ q)
    (hupper : (∫ v, (A v v)^2 ∂stdGaussian E) ≤
      -8*q*(∫ v, A v v ∂stdGaussian E)) :
    -8*(Module.finrank ℝ E : ℝ)*q/((Module.finrank ℝ E : ℝ)+2) ≤
      ∫ v, A v v ∂stdGaussian E := by
  rw [gaussian_integral_bilinear_eq_trace] at hupper ⊢
  exact quadratic_lower_bound_of_square_upper _ _ _ (by exact_mod_cast hd) hq
    ((gaussian_integral_bilinear_sq_ge_trace_sq A hsym hd).trans hupper)
end Preiss
#print axioms Preiss.quadratic_lower_bound_of_square_upper
#print axioms Preiss.gaussian_bilinear_integral_lower_bound_of_square_upper
