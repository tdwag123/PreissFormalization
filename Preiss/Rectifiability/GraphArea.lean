module

public import Preiss.Rectifiability.Graphs
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def linearJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) : ℝ :=
  Real.sqrt (LinearMap.det ((A.adjoint.comp A).toLinearMap))

theorem map_jacobian_hausdorff_affine_injection (A : Euclidean m →L[ℝ] Euclidean n)
    (hA : Function.Injective A) (b : Euclidean n) :
    (ENNReal.ofReal (linearJacobian A) • ((Measure.hausdorffMeasure (m : ℝ)) : Measure (Euclidean m))).map
      (fun v ↦ A v + b) = ((Measure.hausdorffMeasure (m : ℝ))).restrict (Set.range (fun v ↦ A v + b)) := by sorry

theorem map_withDensity_jacobian_eq_graph_hausdorff
    (V : Plane m n) (f : V.1 → ↥(V.1ᗮ)) {K : ℝ≥0} (hf : LipschitzWith K f) :
    ((Measure.hausdorffMeasure (m : ℝ) : Measure V.1).withDensity
      (fun v ↦ ENNReal.ofReal (linearJacobian (fderiv ℝ (graphMap V f) v)))).map
      (graphMap V f) = ((Measure.hausdorffMeasure (m : ℝ))).restrict (Set.range (graphMap V f)) := by sorry

end Preiss
