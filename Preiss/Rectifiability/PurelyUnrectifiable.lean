module

public import Preiss.Rectifiability.Basic

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def PurelyUnrectifiable (m : ℕ) (E : Set (Euclidean n)) : Prop :=
  ∀ R : Set (Euclidean n), CountablyRectifiable m R → (Measure.hausdorffMeasure (m : ℝ)) (E ∩ R) = 0

theorem purelyUnrectifiable_mono {E F : Set (Euclidean n)}
    (hE : PurelyUnrectifiable m E) (hFE : F ⊆ E) : PurelyUnrectifiable m F := by
  intro R hR
  have hsub : F ∩ R ⊆ E ∩ R := fun _ hx ↦ ⟨hFE hx.1, hx.2⟩
  exact measure_mono_null hsub (hE R hR)

theorem purelyUnrectifiable_measure_inter_eq_zero {E R : Set (Euclidean n)}
    (hE : PurelyUnrectifiable m E) (hR : CountablyRectifiable m R) :
    Measure.hausdorffMeasure (m : ℝ) (E ∩ R) = 0 :=
  hE R hR

end Preiss
