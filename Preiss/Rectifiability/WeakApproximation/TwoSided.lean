module

public import Preiss.Geometry.Cones
public import Mathlib.MeasureTheory.Measure.Basic

/-! # A common-plane two-sided approximation predicate -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

def TwoSidedApproximation (m : ℕ) (μ : Measure (Euclidean n))
    (F G : Set (Euclidean n)) (η γ R : ℝ) : Prop :=
  F.Nonempty ∧ ∀ a ∈ G, ∀ r : ℝ, 0 < r → r < R → ∃ V : Plane m n,
    F ∩ ball a (2 * r) ⊆ closedTube a V (η * r) ∧
    (∀ z : Euclidean n, z - a ∈ V.1 → z ∈ ball a r → infDist z F < η * r) ∧
    (∀ z : Euclidean n, z - a ∈ V.1 → z ∈ ball a r →
      ENNReal.ofReal (γ * (η * r) ^ m) ≤ μ (ball z (η * r)))

end Preiss
