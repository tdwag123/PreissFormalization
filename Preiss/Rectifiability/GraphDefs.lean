module

public import Preiss.Geometry.Planes
public import Preiss.Rectifiability.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-! # Lipschitz graphs over linear planes -/

@[expose] public section
open MeasureTheory
open scoped NNReal

namespace Preiss

/-- A full Lipschitz graph over an m-plane, with values in its orthogonal complement.
Affine translates are included: the graphing function need not vanish at zero.
Containment in countably many such graphs is a separate covering condition. -/
def IsLipschitzGraph {n : ℕ} (m : ℕ) (s : Set (Euclidean n)) : Prop :=
  ∃ (V : Plane m n) (f : V.1 → ↥(V.1ᗮ)),
    (∃ K : ℝ≥0, LipschitzWith K f) ∧
      s = Set.range (fun v : V.1 => (v : Euclidean n) + (f v : Euclidean n))

/-- The book's graph-cover definition for a Borel set. A graph is taken over an
`m`-dimensional linear plane; its Lipschitz function takes values in the orthogonal
complement. The function may have a nonzero value at the origin, so affine graphs
are included. The countable family may be empty. -/
def IsBookRectifiable {n : ℕ} (m : ℕ) (s : Set (Euclidean n)) : Prop :=
  MeasurableSet s ∧
    ∃ G : Set (Set (Euclidean n)), G.Countable ∧
      (∀ Γ ∈ G, IsLipschitzGraph m Γ) ∧
        (MeasureTheory.Measure.hausdorffMeasure (m : ℝ))
          (s \ ⋃ Γ ∈ G, Γ) = 0

end Preiss
