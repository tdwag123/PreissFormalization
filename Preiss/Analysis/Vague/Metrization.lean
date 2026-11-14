import Preiss.Geometry.Euclidean
import Preiss.Analysis.CountableCoordinateMetric
import Preiss.Analysis.Vague.DeterminingTests
import FormalizingGMT.WeakConvergence.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

/-! # A reusable metric presentation of vague convergence

The metric is supplied as data with a specification. Its existence is established below;
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

noncomputable def vagueMetrizationOfDenseCompactTests {n : ℕ}
    (F : DenseCompactTestFamily (Euclidean n)) : VagueMetrization n := by
  let coordinates (j : ℕ) (μ : RegularEuclideanMeasure n) := ∫ x, F.tests j x ∂μ.val
  have hsep (μ ν : RegularEuclideanMeasure n)
      (h : ∀ j, coordinates j μ = coordinates j ν) : μ = ν := by
    apply Subtype.ext
    exact measure_eq_of_denseCompactTests F μ.val ν.val μ.property ν.property h
  refine ⟨F.tests, countableCoordinateMetric coordinates hsep, ?_, ?_, ?_⟩
  · intro μ ν
    exact countableCoordinateMetric_dist coordinates hsep μ ν
  · intro R hR
    exact F.cutoffs (closedBall (0 : Euclidean n) R) (isCompact_closedBall _ _)
  · intro μ ν
    exact (countableCoordinateMetric_tendsto_iff coordinates hsep μ atTop ν).trans
      (weaklyConverges_iff_denseCompactTests F (fun i => (μ i).val) ν.val
        (fun i => (μ i).property) ν.property).symm

theorem exists_vagueMetrization (n : ℕ) : Nonempty (VagueMetrization n) := by
  obtain ⟨F⟩ := exists_denseCompactTestFamily (X := Euclidean n)
  exact ⟨vagueMetrizationOfDenseCompactTests F⟩

theorem vagueMetric_tendsto_iff {n : ℕ} (M : VagueMetrization n)
    (μ : ℕ → RegularEuclideanMeasure n) (ν : RegularEuclideanMeasure n) :
    letI := M.metric
    Tendsto μ atTop (𝓝 ν) ↔ Measure.WeaklyConverges (fun i => (μ i).val) ν.val := by
  exact M.tendsto_iff μ ν

theorem vagueMetric_separates {n : ℕ} (M : VagueMetrization n)
    (μ ν : RegularEuclideanMeasure n) :
    vagueTestDistance M.tests μ ν = 0 ↔ μ = ν := by
  letI := M.metric
  rw [← M.distance_eq μ ν, dist_eq_zero]

theorem vagueMetric_finite_cover_of_compact {n : ℕ} (M : VagueMetrization n)
    (K : Set (RegularEuclideanMeasure n)) :
    letI := M.metric
    IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ F : Set (RegularEuclideanMeasure n),
      F.Finite ∧ F ⊆ K ∧ ∀ μ ∈ K, ∃ ν ∈ F, dist μ ν < ε := by
  letI := M.metric
  intro hK ε hε
  obtain ⟨F, hFK, hF, hcover⟩ := hK.finite_cover_balls hε
  refine ⟨F, hF, hFK, ?_⟩
  intro μ hμ
  obtain ⟨ν, hν⟩ := Set.mem_iUnion.mp (hcover hμ)
  obtain ⟨hνF, hball⟩ := Set.mem_iUnion.mp hν
  exact ⟨ν, hνF, hball⟩

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
  classical
  obtain ⟨M⟩ := exists_vagueMetrization n
  letI := M.metric
  let η (i j : ℕ) : RegularEuclideanMeasure n := ⟨μ i j, hμ i j⟩
  let ζ (i : ℕ) : RegularEuclideanMeasure n := ⟨ν i, hν i⟩
  let ξ' : RegularEuclideanMeasure n := ⟨ξ, hξ⟩
  have hrow (i : ℕ) : Tendsto (η i) atTop (𝓝 (ζ i)) :=
    (M.tendsto_iff (η i) (ζ i)).mpr (hrows i)
  have hseq : Tendsto ζ atTop (𝓝 ξ') := (M.tendsto_iff ζ ξ').mpr hlim
  have hselect (i : ℕ) : ∃ j, i ≤ j ∧ P i j ∧
      dist (ζ i) (η i j) < 1 / ((i : ℝ) + 1) := by
    have hevent := Metric.tendsto_nhds.mp (hrow i) (1 / ((i : ℝ) + 1)) (by positivity)
    have hboth : ∀ᶠ j in atTop, i ≤ j ∧ P i j ∧
        dist (ζ i) (η i j) < 1 / ((i : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop i, hP i, hevent] with j hj hPj hdj
      exact ⟨hj, hPj, by rwa [dist_comm]⟩
    exact hboth.exists
  choose j hjge hjP hjdist using hselect
  have hdist : Tendsto (fun i => dist (ζ i) (η i (j i))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun i => (hjdist i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hdiag := hseq.congr_dist hdist
  exact ⟨j, fun i => ⟨hjge i, hjP i⟩,
    (M.tendsto_iff (fun i => η i (j i)) ξ').mp hdiag⟩

end Preiss
