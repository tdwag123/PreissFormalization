import Preiss.Density.Defs
import FormalizingGMT.MarstrandTheorem

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace Preiss

variable {n : ℕ}

/-- An m-plane through the origin. Do not assume a topology on this subtype:
the compact Grassmannian model via orthogonal projections is a separate task. -/
abbrev Plane (m n : ℕ) := {V : Submodule ℝ (Euclidean n) // Module.finrank ℝ V = m}

/-- Flat measures form a cone: all positive finite multiples are included. -/
def IsFlat (m : ℕ) (ν : Measure (Euclidean n)) : Prop :=
  ∃ V : Plane m n, ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧
    ν = c • (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n))

/-- Fixed dimensional normalization, as in De Lellis. This is NOT the
arbitrary scalar sequence in FormalizingGMT's `IsTangentMeasure`. -/
noncomputable def dimensionalBlowup (m : ℕ) (μ : Measure (Euclidean n))
    (x : Euclidean n) (r : ℝ) : Measure (Euclidean n) :=
  (ENNReal.ofReal (r ^ m))⁻¹ • μ.map (blowUpMap x r)

def IsDimensionalTangent (m : ℕ) (μ ν : Measure (Euclidean n))
    (x : Euclidean n) : Prop :=
  ν.Regular ∧ ν ≠ 0 ∧ ∃ r : ℕ → ℝ,
    (∀ i, 0 < r i) ∧ Tendsto r atTop (𝓝 0) ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m μ x (r i)) ν

def IsTangentAtInfinity (m : ℕ) (μ ν : Measure (Euclidean n)) : Prop :=
  ν.Regular ∧ ν ≠ 0 ∧ ∃ r : ℕ → ℝ,
    (∀ i, 0 < r i) ∧ Tendsto r atTop atTop ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m μ 0 (r i)) ν

/-- An adapter to the EXISTING uniform-measure definition, with unit mass and
the origin in the support. Only used for `0 < m`. This removes arbitrary
normalization constants from quantitative gap statements. -/
def IsUnitUniform (m : ℕ) (ν : Measure (Euclidean n)) : Prop :=
  IsSUniform (m : ℝ) ν ∧ (0 : Euclidean n) ∈ ν.support ∧ ν (closedBall 0 1) = 1

def IsConical (m : ℕ) (ν : Measure (Euclidean n)) : Prop :=
  ∀ r : ℝ, 0 < r → dimensionalBlowup m ν 0 r = ν

end Preiss
