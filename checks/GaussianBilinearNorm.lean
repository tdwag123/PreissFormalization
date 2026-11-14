import Preiss.Analysis.GaussianQuadraticForms
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Preiss
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem integrable_gaussian_norm_sq_bilinear (A : E →L[ℝ] E →L[ℝ] F) :
    Integrable (fun v => ‖A v v‖ ^ 2) (stdGaussian E) := by
  have h4 : Integrable (fun v : E => ‖v‖ ^ 4) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (4 : ℝ≥0∞) (by norm_num)).integrable_norm_pow'
  apply (h4.const_mul (‖A‖ ^ 2)).mono' (by fun_prop)
  filter_upwards [] with v
  have hA : ‖A v v‖ ≤ ‖A‖ * ‖v‖ ^ 2 := by
    calc
      ‖A v v‖ ≤ ‖A v‖ * ‖v‖ := (A v).le_opNorm v
      _ ≤ (‖A‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg v)
      _ = _ := by ring
  change ‖‖A v v‖ ^ 2‖ ≤ ‖A‖ ^ 2 * ‖v‖ ^ 4
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    ‖A v v‖ ^ 2 ≤ (‖A‖ * ‖v‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 4 := by ring

theorem gaussian_integral_norm_sq_bilinear_of_mean_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ F)
    (A : E →L[ℝ] E →L[ℝ] F) (hsymm : ∀ u v, A u v = A v u)
    (hmean : (∫ v, A v v ∂stdGaussian E) = 0) :
    (∫ v, ‖A v v‖ ^ 2 ∂stdGaussian E) = 2 * ∑ i, ∑ j, ‖A (e i) (e j)‖ ^ 2 := by
  classical
  let Q (l : κ) : E →L[ℝ] E →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ E F ℝ) (innerSL ℝ (f l))).comp A
  have hQ (l : κ) (u v : E) : Q l u v = inner ℝ (f l) (A u v) := rfl
  have htrace (l : κ) : bilinearTrace (Q l) = 0 := by
    rw [← gaussian_integral_bilinear_eq_trace]
    change (∫ v, (innerSL ℝ (f l)) (A v v) ∂stdGaussian E) = 0
    rw [(innerSL ℝ (f l)).integral_comp_comm (integrable_gaussian_bilinear_diagonal A),
      hmean, map_zero]
  have hQint (l : κ) : Integrable (fun v => (Q l v v)^2) (stdGaussian E) := by
    simpa only [Real.norm_eq_abs, sq_abs] using integrable_gaussian_norm_sq_bilinear (Q l)
  have hformula (l : κ) :
      (∫ v, (Q l v v)^2 ∂stdGaussian E) = 2 * ∑ i, ∑ j, (Q l (e i) (e j))^2 := by
    rw [gaussian_integral_bilinear_sq e (Q l) (fun u v => by rw [hQ, hQ, hsymm]),
      htrace, zero_pow (by decide : 2 ≠ 0), zero_add]
  have hdecomp (v : E) : ‖A v v‖^2 = ∑ l, (Q l v v)^2 := by
    simpa only [hQ] using (f.sum_sq_inner_right (A v v)).symm
  simp_rw [hdecomp]
  rw [integral_finsetSum _ (fun l _ => hQint l)]
  simp_rw [hformula]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [hQ] using f.sum_sq_inner_right (A (e i) (e j))

end Preiss

#print axioms Preiss.integrable_gaussian_norm_sq_bilinear
#print axioms Preiss.gaussian_integral_norm_sq_bilinear_of_mean_zero
