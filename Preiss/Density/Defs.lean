import Preiss.Geometry.Euclidean
import FormalizingGMT.Densities.Basic

open MeasureTheory
open scoped ENNReal

namespace Preiss

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Uses FormalizingGMT's closed-ball, diameter-normalized density. -/
def HasPositiveFiniteDensityAt (m : ℕ) (μ : Measure X) (x : X) : Prop :=
  0 < dimensional_lower_density μ.toOuterMeasure (m : ℝ) x ∧
    dimensional_lower_density μ.toOuterMeasure (m : ℝ) x =
      dimensional_upper_density μ.toOuterMeasure (m : ℝ) x ∧
    dimensional_upper_density μ.toOuterMeasure (m : ℝ) x < ∞

/-- The weaker density assumption used by the Marstrand--Mattila criterion. -/
def HasPositiveFiniteDensitiesAt (m : ℕ) (μ : Measure X) (x : X) : Prop :=
  0 < dimensional_lower_density μ.toOuterMeasure (m : ℝ) x ∧
    dimensional_upper_density μ.toOuterMeasure (m : ℝ) x < ∞

theorem HasPositiveFiniteDensityAt.hasDensity {m : ℕ} {μ : Measure X} {x : X}
    (h : HasPositiveFiniteDensityAt m μ x) : HasDensity μ.toOuterMeasure (m : ℝ) x :=
  density_exists_of_lower_eq_upper (m : ℝ) x h.2.1

theorem HasPositiveFiniteDensityAt.densities {m : ℕ} {μ : Measure X} {x : X}
    (h : HasPositiveFiniteDensityAt m μ x) : HasPositiveFiniteDensitiesAt m μ x :=
  ⟨h.1, h.2.2⟩

end Preiss
