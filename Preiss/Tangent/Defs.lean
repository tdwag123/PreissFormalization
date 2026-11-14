import Preiss.Tangent.Blowup
import FormalizingGMT.WeakConvergence.Basic

/-! # Dimensional tangents and tangents at infinity

These use FormalizingGMT's compact-test weak convergence and fixed dimensional scaling.
-/

open MeasureTheory Filter Topology
namespace Preiss
variable {n : Nat}

def IsDimensionalTangent (m : ℕ) (μ ν : Measure (Euclidean n))
    (x : Euclidean n) : Prop :=
  ν.Regular ∧ ν ≠ 0 ∧ ∃ r : ℕ → ℝ,
    (∀ i, 0 < r i) ∧ Tendsto r atTop (𝓝 0) ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m μ x (r i)) ν

def IsTangentAtInfinity (m : ℕ) (μ ν : Measure (Euclidean n)) : Prop :=
  ν.Regular ∧ ν ≠ 0 ∧ ∃ r : ℕ → ℝ,
    (∀ i, 0 < r i) ∧ Tendsto r atTop atTop ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m μ 0 (r i)) ν

end Preiss
