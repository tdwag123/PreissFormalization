module

public import Preiss.Geometry.Planes
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Weak linear approximation

The generic predicate records concentration near a plane and a lower mass bound
at every plane centre. Its set version applies it to restricted Hausdorff measure.
The constants are permitted to depend on the requested aperture.
-/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {n : ℕ}

/-- Two-sided weak linear approximation of a measure at a point. -/
def MeasureWeaklyLinearlyApproximableAt (m : ℕ) (μ : Measure (Euclidean n))
    (x : Euclidean n) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r < r₀ → ∃ V : Plane m n,
      μ (ball x r \ {z | infDist (z - x) (V.1 : Set (Euclidean n)) ≤ η * r})
        < ENNReal.ofReal (η * r ^ m) ∧
      ∀ z : Euclidean n, z - x ∈ V.1 → z ∈ ball x r →
        ENNReal.ofReal (a * r ^ m) ≤ μ (ball z (η * r))

/-- Weak linear approximation of a set, using mathlib's Hausdorff normalization.
Measurability of the carrier is assumed by theorems that require it. -/
def WeaklyLinearlyApproximableAt (m : ℕ) (s : Set (Euclidean n))
    (x : Euclidean n) : Prop :=
  MeasureWeaklyLinearlyApproximableAt m
    ((Measure.hausdorffMeasure (m : ℝ)).restrict s) x

end Preiss
