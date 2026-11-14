module

public import Preiss.Rectifiability.WeakApproximation.Basic
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def negligibleDeletionAt (m : ℕ) (μ : Measure (Euclidean n))
    (s : Set (Euclidean n)) (x : Euclidean n) : Prop :=
  Tendsto (fun r : ℝ ↦ μ (ball x (2 * r) \ s) / ENNReal.ofReal (r ^ m))
    (𝓝[>] 0) (𝓝 0)

theorem weakApproximation_restrict_of_negligible_sdiff
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (F : Set (Euclidean n)) (hF : MeasurableSet F) (x : Euclidean n)
    (h : MeasureWeaklyLinearlyApproximableAt m μ x)
    (herr : negligibleDeletionAt m μ F x) :
    MeasureWeaklyLinearlyApproximableAt m (μ.restrict F) x := by sorry

end Preiss
