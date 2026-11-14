module

public import Preiss.Geometry.Projections
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def rankProjectionSet (m n : ℕ) : Set (Euclidean n →L[ℝ] Euclidean n) :=
  {P | P.adjoint = P ∧ P.comp P = P ∧ Module.finrank ℝ (LinearMap.range P.toLinearMap) = m}

theorem range_planeProjection :
    Set.range (planeProjection (m := m) (n := n)) = rankProjectionSet m n := by sorry

theorem isCompact_rankProjectionSet (m n : ℕ) : IsCompact (rankProjectionSet m n) := by sorry

end Preiss
