module

public import Preiss.Rectifiability.WeakApproximation.Basic
public import Preiss.Geometry.PlaneTopology
public import Preiss.Geometry.Cones
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def weakApproximationGoodSet (m : ℕ) (μ : Measure (Euclidean n)) (η a R : ℝ) :
    Set (Euclidean n) :=
  {x | ∀ r : ℝ, 0 < r → r < R → ∃ V : Plane m n,
    μ (ball x r \ closedTube x V (η * r)) ≤ ENNReal.ofReal (η * r ^ m) ∧
    ∀ z : Euclidean n, z - x ∈ V.1 → z ∈ ball x r →
      ENNReal.ofReal (a * r ^ m) ≤ μ (closedBall z (η * r))}

theorem isClosed_weakApproximationGoodSet (μ : Measure (Euclidean n))
    [IsFiniteMeasure μ] [μ.Regular] {η a R : ℝ}
    (hη : 0 < η) (ha : 0 < a) (hR : 0 < R) :
    IsClosed (weakApproximationGoodSet m μ η a R) := by sorry

theorem weaklyLinearlyApproximableAt_iff_goodSet_exhaustion
    (μ : Measure (Euclidean n)) (x : Euclidean n) :
    MeasureWeaklyLinearlyApproximableAt m μ x ↔
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, x ∈
        weakApproximationGoodSet m μ η (1 / (N + 1 : ℝ)) (1 / (N + 1 : ℝ)) := by sorry

theorem exists_compact_uniform_weakApproximation_subset
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ] [μ.Regular]
    (E : Set (Euclidean n)) (hE : MeasurableSet E)
    (hw : ∀ᵐ x ∂μ.restrict E, MeasureWeaklyLinearlyApproximableAt m μ x)
    (A : Finset ℝ) (hA : ∀ η ∈ A, 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set (Euclidean n), IsCompact C ∧ C ⊆ E ∧
      μ (E \ C) < ENNReal.ofReal ε ∧ ∀ η ∈ A, ∃ N : ℕ,
        C ⊆ weakApproximationGoodSet m μ η (1 / (N + 1 : ℝ)) (1 / (N + 1 : ℝ)) := by sorry

theorem subset_tube_of_lower_mass_and_small_outside_mass
    (μ : Measure (Euclidean n)) (C : Set (Euclidean n)) (a : Euclidean n)
    (V : Plane m n) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hr : 0 < r)
    (hlower : ∀ z ∈ C, ENNReal.ofReal (δ * (η * r / 2) ^ m) ≤
      μ (ball z (η * r / 2)))
    (herror : μ (ball a (2 * r) \ closedTube a V (η * r / 2)) <
      ENNReal.ofReal (δ * (η * r / 2) ^ m)) :
    C ∩ ball a r ⊆ closedTube a V (η * r) := by sorry

end Preiss
