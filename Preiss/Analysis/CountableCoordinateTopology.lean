module

public import Preiss.Analysis.CountableCoordinateMetric
public import Mathlib.Topology.Bases

/-! # Second countability of countable-coordinate metrics -/

@[expose] public section
namespace Preiss
variable {A : Type*}
theorem countableCoordinateMetric_secondCountable (f : ℕ → A → ℝ)
    (hsep : ∀ a b, (∀ j, f j a = f j b) → a = b) :
    letI := countableCoordinateMetric f hsep
    SecondCountableTopology A := by
  letI : MetricSpace (ℕ → ℝ) := PiCountable.metricSpace
  letI := countableCoordinateMetric f hsep
  exact TopologicalSpace.secondCountableTopology_induced A (ℕ → ℝ) (countableCoordinateMap f)
end Preiss
