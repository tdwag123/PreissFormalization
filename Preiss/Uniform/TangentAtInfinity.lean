import Preiss.Uniform.Defs
import Preiss.Tangent.Defs

open MeasureTheory Filter
open scoped Topology
namespace Preiss
variable {n m : ℕ}

theorem unique_tangent_at_infinity (hm : 0 < m) (hmn : m ≤ n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ ξ : Measure (Euclidean n), IsUnitUniform m ξ ∧
      ∀ ζ, IsTangentAtInfinity m ν ζ ↔ ζ = ξ := by
  sorry

theorem blowdown_sequence_converges (hm : 0 < m) (hmn : m ≤ n)
    (ν ξ : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hξ : IsTangentAtInfinity m ν ξ) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hrInfinity : Tendsto r atTop atTop) :
    Measure.WeaklyConverges (fun i => dimensionalBlowup m ν 0 (r i)) ξ := by
  sorry

theorem tangent_at_infinity_conical (hm : 0 < m) (hmn : m ≤ n)
    (ν ξ : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hξ : IsTangentAtInfinity m ν ξ) : IsConical m ξ := by
  sorry

end Preiss
