import Preiss.Uniform.FlatnessContinuity
import Preiss.Uniform.Defs
import Preiss.Tangent.Defs
import Preiss.Density.Defs

open MeasureTheory Set Filter
open scoped Topology CompactlySupported
namespace Preiss
variable {n m : ℕ}

def IsFlatnessGap (m : ℕ) (φ : C_c(Euclidean n, ℝ)) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ ν : Measure (Euclidean n), IsUnitUniform m ν → IsConical m ν →
    flatness m φ ν ≤ ε → IsFlat m ν

theorem exists_flatnessGap (hm : 0 < m) (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ) :
    ∃ ε : ℝ, IsFlatnessGap m φ ε := by
  sorry

/-- Scale data record the whole interval bound, not merely an equality at one crossing. -/
def FirstCrossingData (m : ℕ) (μ : Measure (Euclidean n)) (x : Euclidean n)
    (φ : C_c(Euclidean n, ℝ)) (ε : ℝ) (α ξ : Measure (Euclidean n))
    (r σ : ℕ → ℝ) : Prop :=
  (∀ i, 0 < σ i ∧ σ i ≤ r i) ∧ Tendsto r atTop (𝓝 0) ∧
  Measure.WeaklyConverges (fun i => dimensionalBlowup m μ x (r i)) α ∧
  Measure.WeaklyConverges (fun i => dimensionalBlowup m μ x (σ i)) ξ ∧
  flatness m φ ξ = ε ∧
  (∀ i, flatness m φ (dimensionalBlowup m μ x (σ i)) = ε) ∧
  ∀ i t, t ∈ Icc (σ i) (r i) → flatness m φ (dimensionalBlowup m μ x t) ≤ ε

theorem exists_first_crossing_sequences (hm : 0 < m) (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (ε : ℝ) (hε : IsFlatnessGap m φ ε)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x)
    (hu : ∀ ν, IsDimensionalTangent m μ ν x → IsUnitUniform m ν)
    (α ζ : Measure (Euclidean n)) (hα : IsDimensionalTangent m μ α x)
    (hαflat : IsFlat m α) (hζ : IsDimensionalTangent m μ ζ x) (hζnotflat : ¬ IsFlat m ζ) :
    ∃ (ξ : Measure (Euclidean n)) (r σ : ℕ → ℝ), IsUnitUniform m ξ ∧
      IsDimensionalTangent m μ ξ x ∧ FirstCrossingData m μ x φ ε α ξ r σ := by
  sorry

theorem first_crossing_ratio_tendsto_atTop (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (x : Euclidean n)
    (α ξ : Measure (Euclidean n)) (hα : IsFlat m α) (hξ : IsUnitUniform m ξ)
    (r σ : ℕ → ℝ) (hcross : FirstCrossingData m μ x φ ε α ξ r σ) :
    Tendsto (fun i => r i / σ i) atTop atTop := by
  sorry

theorem first_crossing_limit_flat_at_infinity (hm : 0 < m) (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (ε : ℝ) (hε : IsFlatnessGap m φ ε)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (x : Euclidean n)
    (α ξ : Measure (Euclidean n)) (hξ : IsUnitUniform m ξ)
    (r σ : ℕ → ℝ) (hcross : FirstCrossingData m μ x φ ε α ξ r σ)
    (hratio : Tendsto (fun i => r i / σ i) atTop atTop) :
    (∀ R ≥ 1, flatness m φ (dimensionalBlowup m ξ 0 R) ≤ ε) ∧
    ∀ ψ, IsTangentAtInfinity m ξ ψ → IsFlat m ψ := by
  sorry

end Preiss
