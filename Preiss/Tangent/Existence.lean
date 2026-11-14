import Preiss.Density.Defs
import FormalizingGMT.MarstrandTheorem

/-! # Existence of nonzero tangent measures

These interfaces connect the reusable definitions to the upstream conventions.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem tangent_exists (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) (h : HasPositiveFiniteDensitiesAt m μ x) :
    ∃ ν, IsTangentMeasure μ ν x := by
  have hx : x ∈ positiveFiniteDensitySet (m : ℝ) μ :=
    ⟨h.1, lower_le_upper_density (m : ℝ) x, h.2⟩
  obtain ⟨p, q, R, hp, hq, hR, hup, hlo⟩ := SUniformAux.ball_bounds_of_mem hx
  obtain ⟨_, ν, _, hν, _⟩ := exists_subseq_blowUp_weaklyConverges_tangentMeasure μ
    inferInstance x (mem_support_of_ball_lower_bound hp hR hlo)
    (limsup_ball_ratio_lt_top_of_ball_bounds_at hp hq hR hup hlo)
    (fun i => 1 / ((i : ℝ) + 1)) (fun i => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨ν, hν⟩


end Preiss
