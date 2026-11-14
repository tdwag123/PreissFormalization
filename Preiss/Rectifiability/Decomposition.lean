module

public import Preiss.Rectifiability.PurelyUnrectifiable
public import Preiss.Rectifiability.EuclideanCarrier
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_rectifiable_purelyUnrectifiable_partition (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) :
    ∃ R U : Set (Euclidean n), MeasurableSet R ∧ MeasurableSet U ∧
      Disjoint R U ∧ R ∪ U = E ∧ CountablyRectifiable m R ∧ PurelyUnrectifiable m U := by
  sorry

theorem rectifiable_pure_partition_unique {E R U R' U' : Set (Euclidean n)}
    (hunion : R ∪ U = E) (hunion' : R' ∪ U' = E)
    (hR : CountablyRectifiable m R) (hR' : CountablyRectifiable m R')
    (hU : PurelyUnrectifiable m U) (hU' : PurelyUnrectifiable m U') :
    Measure.hausdorffMeasure (m : ℝ) (R \ R') = 0 ∧
      Measure.hausdorffMeasure (m : ℝ) (R' \ R) = 0 ∧
      Measure.hausdorffMeasure (m : ℝ) (U \ U') = 0 ∧
      Measure.hausdorffMeasure (m : ℝ) (U' \ U) = 0 := by
  refine ⟨measure_mono_null ?_ (hU' R hR),
    measure_mono_null ?_ (hU R' hR'),
    measure_mono_null ?_ (hU R' hR'),
    measure_mono_null ?_ (hU' R hR)⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R' ∪ U' := by
      rw [hunion', ← hunion]
      exact Or.inl hx
    exact ⟨hxE.resolve_left hx', hx⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R ∪ U := by
      rw [hunion, ← hunion']
      exact Or.inl hx
    exact ⟨hxE.resolve_left hx', hx⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R' ∪ U' := by
      rw [hunion', ← hunion]
      exact Or.inr hx
    exact ⟨hx, hxE.resolve_right hx'⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R ∪ U := by
      rw [hunion, ← hunion']
      exact Or.inr hx
    exact ⟨hx, hxE.resolve_right hx'⟩

end Preiss
