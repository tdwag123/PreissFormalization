import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! Reusable definitions. No local finiteness is built into rectifiability. -/
open MeasureTheory Set
open scoped ENNReal NNReal

namespace Preiss

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Exact countable coverage by Lipschitz images of Euclidean space.
Using a countable set of maps permits an empty covering, even for an empty target. -/
def CountablyLipschitzCovered (m : ℕ) (s : Set X) : Prop :=
  ∃ F : Set (Euclidean m → X), F.Countable ∧
    (∀ f ∈ F, ∃ K : ℝ≥0, LipschitzWith K f) ∧
    s ⊆ ⋃ f ∈ F, Set.range f

/-- Countable rectifiability of a set, modulo Hausdorff-null sets.
Measurability and finite Hausdorff measure are separate hypotheses. -/
def CountablyRectifiable (m : ℕ) (s : Set X) : Prop :=
  ∃ t : Set X, CountablyLipschitzCovered m t ∧
    (Measure.hausdorffMeasure (m : ℝ) : Measure X) (s \ t) = 0

/-- A rectifiable measure is absolutely continuous with respect to Hausdorff
measure and is carried by a countably Lipschitz covered set.
Concentration alone would incorrectly admit atoms when `m > 0`. -/
def IsRectifiableMeasure (m : ℕ) (μ : Measure X) : Prop :=
  μ ≪ Measure.hausdorffMeasure (m : ℝ) ∧
    ∃ s : Set X, CountablyLipschitzCovered m s ∧ μ sᶜ = 0

end Preiss
