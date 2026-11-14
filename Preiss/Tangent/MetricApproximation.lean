import Preiss.Analysis.Vague.Metrization
import Preiss.Tangent.Defs
import Preiss.Tangent.BlowupSupport
import Mathlib.Tactic.Push

/-! # Metric approximation and separation of dimensional tangents -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem dimensionalTangent_of_metric_approximation (M : VagueMetrization n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (a : Euclidean n)
    (η : RegularEuclideanMeasure n) (hη : η.val ≠ 0) :
    letI := M.metric
    (∀ ε > 0, ∀ δ > 0, ∃ (r : ℝ) (hr : 0 < r), r < δ ∧
      dist (⟨dimensionalBlowup m μ a r, regular_dimensionalBlowup μ inferInstance a hr⟩ :
        RegularEuclideanMeasure n) η < ε) → IsDimensionalTangent m μ η.val a := by
  classical
  letI := M.metric
  intro h
  choose r hr hsmall hclose using fun i : ℕ =>
    h (1 / ((i : ℝ) + 1)) (by positivity) (1 / ((i : ℝ) + 1)) (by positivity)
  have hr0 : Tendsto r atTop (𝓝 0) := squeeze_zero (fun i => (hr i).le)
    (fun i => (hsmall i).le) tendsto_one_div_add_atTop_nhds_zero_nat
  let τ (i : ℕ) : RegularEuclideanMeasure n :=
    ⟨dimensionalBlowup m μ a (r i), regular_dimensionalBlowup μ inferInstance a (hr i)⟩
  have ht : Tendsto τ atTop (𝓝 η) := tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) (fun i => (hclose i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  exact ⟨η.property, hη, r, hr, hr0, (M.tendsto_iff τ η).mp ht⟩

theorem exists_metric_separation_of_not_dimensionalTangent (M : VagueMetrization n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (a : Euclidean n)
    (η : RegularEuclideanMeasure n) (hη : η.val ≠ 0)
    (hnot : ¬ IsDimensionalTangent m μ η.val a) :
    letI := M.metric
    ∃ ε > 0, ∃ δ > 0, ∀ (r : ℝ) (hr : 0 < r), r < δ →
      ε ≤ dist (⟨dimensionalBlowup m μ a r, regular_dimensionalBlowup μ inferInstance a hr⟩ :
        RegularEuclideanMeasure n) η := by
  classical
  letI := M.metric
  have h := mt (dimensionalTangent_of_metric_approximation M μ a η hη) hnot
  push_neg at h
  exact h

end Preiss
