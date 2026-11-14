module

public import Preiss.Geometry.Planes
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public import Mathlib.Topology.MetricSpace.HausdorffDistance

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

theorem infDist_submodule_eq_norm_sub_starProjection
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] (x : E) :
    infDist x (V : Set E) = ‖x - V.starProjection x‖ := by
  rw [Submodule.starProjection_minimal, infDist_eq_iInf]
  change (⨅ y : V, dist x y) = ⨅ y : V, ‖x - y‖
  simp only [dist_eq_norm]

end Preiss
