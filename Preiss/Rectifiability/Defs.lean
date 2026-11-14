module

public import Preiss.Geometry.Euclidean
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Rectifiable sets and measures

Parametrizations have arbitrary Euclidean domains. Exact coverage, coverage modulo
Hausdorff-null sets, and rectifiability of a measure are separate predicates.
-/

@[expose] public section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace Preiss

/-- A Lipschitz parametrization whose domain is an arbitrary subset of Euclidean space.
The domain can be empty. No measurability assumption is built into this geometric object. -/
structure LipschitzPiece (m : ℕ) (X : Type*) [MetricSpace X] where
  domain : Set (Euclidean m)
  toFun : domain → X
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K toFun

namespace LipschitzPiece
variable {m : ℕ} {X : Type*} [MetricSpace X]

instance : CoeFun (LipschitzPiece m X) (fun p => p.domain → X) :=
  ⟨fun p => p.toFun⟩

/-- The image of a partial-domain Lipschitz parametrization. -/
def range (p : LipschitzPiece m X) : Set X := Set.range p.toFun

end LipschitzPiece

section Coverage
variable {X : Type*} [MetricSpace X]

/-- Exact countable coverage by Lipschitz parametrizations on arbitrary domains.
Using a countable set permits the empty family, even if the target is empty. -/
def CountablyCoveredByLipschitzPieces (m : ℕ) (s : Set X) : Prop :=
  ∃ F : Set (LipschitzPiece m X), F.Countable ∧
    s ⊆ ⋃ p ∈ F, p.range

/-- Existing full-domain convenience predicate, kept distinct from partial-domain coverage.
Its equivalence with partial-domain coverage needs an extension theorem for the target. -/
def CountablyLipschitzCovered (m : ℕ) (s : Set X) : Prop :=
  ∃ F : Set (Euclidean m → X), F.Countable ∧
    (∀ f ∈ F, ∃ K : ℝ≥0, LipschitzWith K f) ∧
    s ⊆ ⋃ f ∈ F, Set.range f

end Coverage

section Rectifiability
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Countable m-rectifiability modulo Hausdorff-null sets.
Measurability and finiteness of Hausdorff measure are separate hypotheses. -/
def CountablyRectifiable (m : ℕ) (s : Set X) : Prop :=
  ∃ t : Set X, CountablyCoveredByLipschitzPieces m t ∧
    (Measure.hausdorffMeasure (m : ℝ) : Measure X) (s \ t) = 0

/-- A rectifiable measure is absolutely continuous with respect to Hausdorff measure
and is carried by a countably rectifiable set. Local finiteness is a separate hypothesis. -/
def IsRectifiableMeasure (m : ℕ) (μ : Measure X) : Prop :=
  μ ≪ Measure.hausdorffMeasure (m : ℝ) ∧
    ∃ s : Set X, CountablyRectifiable m s ∧ μ sᶜ = 0

end Rectifiability

end Preiss
