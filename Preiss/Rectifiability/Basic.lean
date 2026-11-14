module

public import Preiss.Rectifiability.Defs

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem countablyRectifiable_mono {s t : Set X}
    (ht : CountablyRectifiable m t) (hst : s ⊆ t) : CountablyRectifiable m s := by sorry

theorem countablyRectifiable_iUnion (s : ℕ → Set X)
    (hs : ∀ i, CountablyRectifiable m (s i)) : CountablyRectifiable m (⋃ i, s i) := by sorry

theorem countablyRectifiable_image {s : Set X} (hs : CountablyRectifiable m s)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    CountablyRectifiable m (f '' s) := by sorry

theorem countablyRectifiable_of_sdiff_null {s t : Set X}
    (ht : CountablyRectifiable m t)
    (hnull : (Measure.hausdorffMeasure (m : ℝ) : Measure X) (s \ t) = 0) :
    CountablyRectifiable m s := by sorry

theorem isRectifiableMeasure_of_countable_restrict (μ : Measure (Euclidean n))
    (S : ℕ → Set (Euclidean n)) (hS : ∀ i, MeasurableSet (S i))
    (hcover : μ (⋃ i, S i)ᶜ = 0)
    (hrect : ∀ i, IsRectifiableMeasure m (μ.restrict (S i))) :
    IsRectifiableMeasure m μ := by sorry

end Preiss
