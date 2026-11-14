module
public import Preiss.Uniform.MomentCoefficients
public import Preiss.Uniform.Defs
public import Preiss.Analysis.BilinearTrace

@[expose] public section
open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem trace_gaussianMomentForm_two (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (s : ℝ) (hs : 0 < s) :
    bilinearTrace (momentBilinear (gaussianMomentForm μ 2 s)) = (m : ℝ) * s := by
  sorry

theorem trace_secondMomentCoefficient_eq_zero
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B) :
    bilinearTrace (momentBilinear (B 2 2)) = 0 := by
  sorry

end Preiss
