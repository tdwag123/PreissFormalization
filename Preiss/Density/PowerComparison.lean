module

public import Preiss.Geometry.Euclidean
public import Preiss.Analysis.HausdorffComparison
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def UpperPowerBoundAt (m : ℕ) (μ : Measure (Euclidean n)) (x : Euclidean n) : Prop :=
  ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ m)

theorem measure_restrict_le_hausdorff_of_ball_bounds (m n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
      (S : Set (Euclidean n)) (b R : ℝ), MeasurableSet S → 0 < b → 0 < R →
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r < R → μ (ball x r) ≤ ENNReal.ofReal (b * r ^ m)) →
      μ.restrict S ≤ ENNReal.ofReal (C * b) • ((Measure.hausdorffMeasure (m : ℝ))).restrict S := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro μ _ S b R hS hb hR hball
  simpa only [one_mul] using
    measure_restrict_le_hausdorff_of_uniform_ball_upper_bound m μ S hS b R hb hR hball

theorem hausdorff_restrict_le_measure_of_ball_bounds (m n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
      (S : Set (Euclidean n)) (a R : ℝ), MeasurableSet S → 0 < a → 0 < R →
      (∀ x ∈ S, ∀ r : ℝ, 0 < r → r < R → ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r)) →
      ((Measure.hausdorffMeasure (m : ℝ))).restrict S ≤ ENNReal.ofReal (C / a) • μ.restrict S := by sorry

end Preiss
