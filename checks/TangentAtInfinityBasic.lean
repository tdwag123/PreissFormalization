module
public import Preiss.Uniform.Compactness
public import Preiss.Tangent.Defs
public import Mathlib.Tactic

@[expose] public section
namespace Preiss
open MeasureTheory Filter Set Metric
open scoped Topology CompactlySupported
variable {n m : ℕ}

theorem IsUnitUniform.ne_zero (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ) :
    μ ≠ 0 := by
  intro h
  simpa only [h, Measure.support_zero, Set.mem_empty_iff_false] using hμ.2.1

theorem isUnitUniform_of_tangentAtInfinity
    (μ ν : Measure (Euclidean n)) (hμ : IsUnitUniform m μ)
    (hν : IsTangentAtInfinity m μ ν) : IsUnitUniform m ν := by
  obtain ⟨hreg, _, r, hr, _, hlim⟩ := hν
  exact isUnitUniform_of_vague _
    (fun i => isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i)) ν hreg hlim

theorem exists_unitUniform_tangentAtInfinity
    (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ) :
    ∃ ν, IsUnitUniform m ν ∧ IsTangentAtInfinity m μ ν := by
  let r : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hr (i : ℕ) : 0 < r i := by dsimp [r]; positivity
  have hrinf : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨φ, ν, hφ, hν, hlim⟩ := exists_vague_subsequence_unitUniform
    (fun i => dimensionalBlowup m μ 0 (r i))
    (fun i => isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i))
  exact ⟨ν, hν, hν.1, IsUnitUniform.ne_zero ν hν,
    r ∘ φ, fun i => hr (φ i), hrinf.comp hφ.tendsto_atTop, hlim⟩


end Preiss
