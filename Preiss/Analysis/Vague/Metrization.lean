import Preiss.Analysis.Vague.CompactTests
import Mathlib.Topology.MetricSpace.Defs

/-! # A reusable metric presentation of vague convergence

The metric is supplied as data with a specification. Its existence is a theorem obligation;
no definition chooses data from an unfinished theorem.
-/

open MeasureTheory Filter Set Metric
open scoped Topology CompactlySupported
noncomputable section
namespace Preiss

abbrev RegularEuclideanMeasure (n : ℕ) :=
  {μ : Measure (Euclidean n) // μ.Regular}

/-- Weighted distance determined by a countable family of compactly supported tests. -/
def vagueTestDistance {n : ℕ} (f : ℕ → C_c(Euclidean n, ℝ))
    (μ ν : RegularEuclideanMeasure n) : ℝ :=
  ∑' j : ℕ, (2 : ℝ)⁻¹ ^ (j + 1) *
    min 1 |(∫ x, f j x ∂μ.val) - ∫ x, f j x ∂ν.val|

/-- A countable-test metric on all regular Euclidean measures, with cutoff tests and
the exact sequential convergence specification. -/
structure VagueMetrization (n : ℕ) where
  tests : ℕ → C_c(Euclidean n, ℝ)
  metric : MetricSpace (RegularEuclideanMeasure n)
  distance_eq : letI := metric
    ∀ μ ν, dist μ ν = vagueTestDistance tests μ ν
  cutoffs : ∀ R : ℝ, 0 < R → ∃ j,
    (∀ x, 0 ≤ tests j x) ∧ ∀ x ∈ closedBall (0 : Euclidean n) R, 1 ≤ tests j x
  tendsto_iff : ∀ (μ : ℕ → RegularEuclideanMeasure n) (ν : RegularEuclideanMeasure n),
    letI := metric
    Tendsto μ atTop (𝓝 ν) ↔ Measure.WeaklyConverges (fun i => (μ i).val) ν.val

theorem exists_vagueMetrization (n : ℕ) : Nonempty (VagueMetrization n) := by
  sorry

theorem vagueMetric_tendsto_iff {n : ℕ} (M : VagueMetrization n)
    (μ : ℕ → RegularEuclideanMeasure n) (ν : RegularEuclideanMeasure n) :
    letI := M.metric
    Tendsto μ atTop (𝓝 ν) ↔ Measure.WeaklyConverges (fun i => (μ i).val) ν.val := by
  sorry

theorem vagueMetric_separates {n : ℕ} (M : VagueMetrization n)
    (μ ν : RegularEuclideanMeasure n) :
    vagueTestDistance M.tests μ ν = 0 ↔ μ = ν := by
  sorry

theorem vagueMetric_finite_cover_of_compact {n : ℕ} (M : VagueMetrization n)
    (K : Set (RegularEuclideanMeasure n)) :
    letI := M.metric
    IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ F : Set (RegularEuclideanMeasure n),
      F.Finite ∧ F ⊆ K ∧ ∀ μ ∈ K, ∃ ν ∈ F, dist μ ν < ε := by
  sorry

/-- A single eventual condition can encode any finite collection of stagewise constraints. -/
theorem vague_diagonal_selection {n : ℕ}
    (μ : ℕ → ℕ → Measure (Euclidean n)) (ν : ℕ → Measure (Euclidean n))
    (ξ : Measure (Euclidean n)) (hμ : ∀ i j, (μ i j).Regular)
    (hν : ∀ i, (ν i).Regular) (hξ : ξ.Regular)
    (hrows : ∀ i, Measure.WeaklyConverges (μ i) (ν i))
    (hlim : Measure.WeaklyConverges ν ξ) (P : ℕ → ℕ → Prop)
    (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ j : ℕ → ℕ, (∀ i, i ≤ j i ∧ P i (j i)) ∧
      Measure.WeaklyConverges (fun i => μ i (j i)) ξ := by
  sorry

end Preiss
