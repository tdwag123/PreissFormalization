module
public import Preiss.Uniform.MomentCoefficients
public import Preiss.Uniform.Defs
public import Preiss.Analysis.BilinearTrace

@[expose] public section
open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem conical_gaussianMoment_homogeneous (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    gaussianMomentForm μ k s = s ^ ((k : ℝ) / 2) • gaussianMomentForm μ k 1 := by
  sorry

theorem conical_gaussianMoment_odd (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (k : ℕ) (hk : Odd k) (s : ℝ) (hs : 0 < s) : gaussianMomentForm μ k s = 0 := by
  sorry

theorem conical_covariance_trace_support (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ) :
    (∀ x : Euclidean n, 0 ≤ gaussianMomentForm μ 2 1 (fun _ => x)) ∧
    bilinearTrace (momentBilinear (gaussianMomentForm μ 2 1)) = (m : ℝ) ∧
    ∀ x ∈ μ.support, gaussianMomentForm μ 2 1 (fun _ => x) = ‖x‖ ^ 2 := by
  sorry

end Preiss
