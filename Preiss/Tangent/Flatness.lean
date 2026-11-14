import Preiss.Uniform.FlatnessContinuity
import Preiss.Tangent.Blowup

open MeasureTheory Set
open scoped CompactlySupported
namespace Preiss
variable {n m : ℕ}

theorem continuousOn_flatness_dimensionalBlowup (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (x : Euclidean n) :
    ContinuousOn (fun r => flatness m φ (dimensionalBlowup m μ x r)) (Ioi 0) := by
  sorry

end Preiss
