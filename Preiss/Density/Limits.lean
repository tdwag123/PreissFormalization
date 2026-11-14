import FormalizingGMT.Densities.Basic

/-! # Values of existing dimensional densities

These order-topological lemmas work for outer measures on pseudo extended metric
spaces and arbitrary real dimension parameters. No local finiteness is needed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Preiss
variable {X : Type*} [PseudoEMetricSpace X] {μ : OuterMeasure X} {s : ℝ} {x : X}

theorem dimensional_density_eq_of_tendsto {θ : ℝ≥0∞}
    (h : Tendsto (dimensional_density_ratio μ s x) (𝓝[>] 0) (𝓝 θ)) :
    dimensional_density μ s x = θ :=
  le_antisymm (sInf_le h)
    (le_sInf fun y hy => (tendsto_nhds_unique h hy).le)

theorem lower_eq_upper_of_hasDensity (h : HasDensity μ s x) :
    dimensional_lower_density μ s x = dimensional_upper_density μ s x := by
  obtain ⟨θ, hθ⟩ := h.exists_tendsto
  exact hθ.liminf_eq.trans hθ.limsup_eq.symm

theorem density_eq_lower_of_hasDensity (h : HasDensity μ s x) :
    dimensional_density μ s x = dimensional_lower_density μ s x := by
  obtain ⟨θ, hθ⟩ := h.exists_tendsto
  exact (dimensional_density_eq_of_tendsto hθ).trans hθ.liminf_eq.symm

theorem density_eq_upper_of_hasDensity (h : HasDensity μ s x) :
    dimensional_density μ s x = dimensional_upper_density μ s x :=
  (density_eq_lower_of_hasDensity h).trans (lower_eq_upper_of_hasDensity h)

end Preiss
