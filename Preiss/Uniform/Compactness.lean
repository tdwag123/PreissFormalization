import Preiss.Uniform.Scaling
import Preiss.Analysis.Vague.Metrization
import FormalizingGMT.WeakConvergence.CompactnessCriterion

/-! # Closedness and compactness of uniform measure families -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- S05a: regularity of the proposed limit is explicit. -/
theorem isUnitUniform_of_vague (ν : ℕ → Measure (Euclidean n))
    (hν : ∀ i, IsUnitUniform m (ν i)) (ξ : Measure (Euclidean n))
    (hξ : ξ.Regular) (hlim : Measure.WeaklyConverges ν ξ) :
    IsUnitUniform m ξ := by
  sorry

/-- S05b: strict monotonicity keeps the selected sequence a genuine subsequence. -/
theorem exists_vague_subsequence_unitUniform (ν : ℕ → Measure (Euclidean n))
    (hν : ∀ i, IsUnitUniform m (ν i)) :
    ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧ IsUnitUniform m ξ ∧
      Measure.WeaklyConverges (fun i ↦ ν (φ i)) ξ := by
  sorry

/-- S05c: support nonemptiness is part of the ball-law predicate. -/
theorem exists_vague_subsequence_uniform_of_dist_support_tendsto_zero
    (ν : ℕ → Measure (Euclidean n))
    (hν : ∀ i, IsUniformWithConstant m 1 (ν i))
    (hnear : Tendsto (fun i ↦ infDist (0 : Euclidean n) (ν i).support) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧ IsUnitUniform m ξ ∧
      Measure.WeaklyConverges (fun i ↦ ν (φ i)) ξ := by
  sorry

/-- S06c: all ball constants in one fixed positive compact interval are allowed. -/
theorem unitUniform_totallyBounded (M : VagueMetrization n)
    {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    letI := M.metric
    TotallyBounded {ν : RegularEuclideanMeasure n | ∃ q ∈ Icc c C,
      IsUniformWithConstant m q ν.1 ∧ (0 : Euclidean n) ∈ ν.1.support} := by
  sorry

end Preiss
