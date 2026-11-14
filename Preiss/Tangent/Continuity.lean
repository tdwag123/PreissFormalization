import Preiss.Tangent.Blowup
import FormalizingGMT.WeakConvergence.Basic

open MeasureTheory Filter
open scoped Topology
namespace Preiss
variable {n m : ℕ}

theorem vague_smul_map_sub_div (μ : ℕ → Measure (Euclidean n))
    (ν : Measure (Euclidean n)) (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (a : ℕ → Euclidean n) (b : Euclidean n) (ha : Tendsto a atTop (𝓝 b))
    (r : ℕ → ℝ) (s : ℝ) (hr : ∀ i, 0 < r i) (hs : 0 < s)
    (hrs : Tendsto r atTop (𝓝 s)) (c : ℕ → ℝ) (d : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : 0 ≤ d) (hcd : Tendsto c atTop (𝓝 d)) :
    Measure.WeaklyConverges
      (fun i => ENNReal.ofReal (c i) • (μ i).map (fun z => (r i)⁻¹ • (z - a i)))
      (ENNReal.ofReal d • ν.map (fun z => s⁻¹ • (z - b))) := by
  sorry

theorem vague_dimensionalBlowup_moving (μ : ℕ → Measure (Euclidean n))
    (ν : Measure (Euclidean n)) (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (a : ℕ → Euclidean n) (b : Euclidean n) (ha : Tendsto a atTop (𝓝 b))
    (r : ℕ → ℝ) (s : ℝ) (hr : ∀ i, 0 < r i) (hs : 0 < s)
    (hrs : Tendsto r atTop (𝓝 s)) :
    Measure.WeaklyConverges (fun i => dimensionalBlowup m (μ i) (a i) (r i))
      (dimensionalBlowup m ν b s) := by
  sorry

end Preiss
