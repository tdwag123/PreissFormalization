import Preiss.Uniform.Compactness
import Preiss.Tangent.Defs

/-! # Subsequential compactness of uniform blow-downs -/

open MeasureTheory Metric Set Filter Topology
namespace Preiss
variable {m n : ℕ}

/-- M10a: every positive sequence escaping to infinity admits a unit uniform limit. -/
theorem exists_tangentAtInfinity (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrinf : Tendsto r atTop atTop) :
    ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧ IsUnitUniform m ξ ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m ν 0 (r (φ i))) ξ ∧
      IsTangentAtInfinity m ν ξ := by
  obtain ⟨φ, ξ, hφ, hξ, hlim⟩ := exists_vague_subsequence_unitUniform
    (fun i => dimensionalBlowup m ν 0 (r i))
    (fun i => isUnitUniform_dimensionalBlowup ν hν 0 hν.2.1 (hr i))
  refine ⟨φ, ξ, hφ, hξ, hlim, hξ.1, ?_, r ∘ φ, fun i => hr (φ i),
    hrinf.comp hφ.tendsto_atTop, hlim⟩
  intro hzero
  have hsupport := hξ.2.1
  simpa [hzero] using hsupport

end Preiss
