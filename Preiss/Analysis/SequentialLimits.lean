module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Detecting sequence convergence through further subsequences -/

@[expose] public section
open Filter Metric Topology
namespace Preiss

theorem tendsto_of_subsequence_subsequence {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X) (x : X)
    (h : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (f ∘ ψ ∘ ρ) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hnot
  obtain ⟨ψ, hψ, hbad⟩ := extraction_of_frequently_atTop (Filter.not_eventually.mp hnot)
  obtain ⟨ρ, hρ, hconv⟩ := h ψ hψ
  obtain ⟨i, hi⟩ := (Metric.tendsto_nhds.mp hconv ε hε).exists
  exact hbad (ρ i) hi

end Preiss
