import Preiss.Uniform.Compactness
import Preiss.Tangent.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Unit-uniform dimensional tangents at support points -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem exists_unitUniform_dimensionalTangent (ν : Measure (Euclidean n))
    (hν : IsUnitUniform m ν) (y : Euclidean n) (hy : y ∈ ν.support) :
    ∃ ξ : Measure (Euclidean n), IsDimensionalTangent m ν ξ y ∧ IsUnitUniform m ξ := by
  let r (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)
  have hr (i : ℕ) : 0 < r i := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, ξ, hφ, hξ, hlim⟩ := exists_vague_subsequence_unitUniform
    (fun i => dimensionalBlowup m ν y (r i))
    (fun i => isUnitUniform_dimensionalBlowup ν hν y hy (hr i))
  have hξ0 : ξ ≠ 0 := by
    intro hz
    simpa [hz] using hξ.2.1
  exact ⟨ξ, ⟨hξ.1, hξ0, r ∘ φ, fun i => hr (φ i), hr0.comp hφ.tendsto_atTop, hlim⟩, hξ⟩

end Preiss
