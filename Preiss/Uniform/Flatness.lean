module

public import Preiss.Geometry.Planes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Quadratic distance energy and flatness -/

@[expose] public section

open MeasureTheory Metric Set

open scoped CompactlySupported

namespace Preiss
variable {n : ℕ}

noncomputable def flatnessEnergy {m : ℕ} (φ : C_c(Euclidean n, ℝ))
    (ν : Measure (Euclidean n)) (V : Plane m n) : ℝ :=
  ∫ z, φ z * (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂ν

/-- Only use the minimization API with `m ≤ n`; otherwise the plane type is empty. -/
noncomputable def flatness (m : ℕ) (φ : C_c(Euclidean n, ℝ))
    (ν : Measure (Euclidean n)) : ℝ :=
  sInf (Set.range (flatnessEnergy φ ν : Plane m n → ℝ))

end Preiss
