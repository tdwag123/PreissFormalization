module

public import Preiss.Geometry.Planes
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def proj (V : Plane m n) (x : Euclidean n) : Euclidean n :=
  V.1.orthogonalProjectionOnto x

def planeProjection (V : Plane m n) : Euclidean n →L[ℝ] Euclidean n :=
  V.1.starProjection

theorem planeProjection_injective :
    Function.Injective (planeProjection (m := m) (n := n)) := by
  intro V W h
  apply Subtype.ext
  have hr := congrArg (fun P : Euclidean n →L[ℝ] Euclidean n ↦ P.range) h
  simpa only [planeProjection, Submodule.range_starProjection] using hr

end Preiss
