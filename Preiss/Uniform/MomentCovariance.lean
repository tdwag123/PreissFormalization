module
public import Preiss.Uniform.MomentForms
public import Preiss.Tangent.Blowup

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace Preiss
variable {n m : ℕ}

theorem gaussianMomentForm_dilate (μ : Measure (Euclidean n))
    (k : ℕ) (s r : ℝ) (hr : 0 < r) :
    gaussianMomentForm (dimensionalBlowup m μ 0 r) k s =
      (r ^ k) • gaussianMomentForm μ k (s / r ^ 2) := by
  sorry

theorem gaussianMomentForm_smul (μ : Measure (Euclidean n))
    (c : ℝ≥0∞) (hc : 0 < c) (hcfin : c ≠ ∞) (k : ℕ) (s : ℝ) :
    gaussianMomentForm (c • μ) k s = gaussianMomentForm μ k s := by
  have hcr : c.toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos (ne_of_gt hc) hcfin)
  simp [gaussianMomentForm, gaussianMass, integral_smul_measure, smul_smul,
    smul_eq_mul, mul_inv_rev, mul_assoc, hcr]

theorem gaussianMomentForm_map_linearIsometry {d : ℕ}
    (L : Euclidean n →ₗᵢ[ℝ] Euclidean d) (μ : Measure (Euclidean n))
    (k : ℕ) (s : ℝ) (u : Fin k → Euclidean n) :
    gaussianMomentForm (μ.map L) k s (fun i => L (u i)) =
      gaussianMomentForm μ k s u := by
  sorry

end Preiss
