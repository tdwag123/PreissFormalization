import Preiss.Geometry.Euclidean
import FormalizingGMT.WeakConvergence.Basic

open MeasureTheory Filter Set
open scoped Topology CompactlySupported
namespace Preiss
variable {n : ℕ}

theorem vague_integral_moving_compact_test
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (f : ℕ → C_c(Euclidean n, ℝ)) (g : C_c(Euclidean n, ℝ))
    (hfK : ∀ i x, x ∉ K → f i x = 0) (hgK : ∀ x, x ∉ K → g x = 0)
    (hfg : ∀ ε > 0, ∀ᶠ i in atTop, ∀ x, |f i x - g x| < ε) :
    Tendsto (fun i => ∫ x, f i x ∂μ i) atTop (𝓝 (∫ x, g x ∂ν)) := by
  sorry

end Preiss
