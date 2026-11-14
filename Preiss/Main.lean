import Preiss.Density.Dimension
import Preiss.Rectifiability.Zero
import Preiss.Uniform.GMTAdapters
import Preiss.Rectifiability.MarstrandMattila.MeasureCriterion
import Preiss.Theorem.PartA
import Preiss.Theorem.PartB

/-! # Preiss's rectifiability theorem

The assembly proof is explicit. Its intermediate theorem obligations currently
contain `sorry`, so this is not yet a completed formal proof of Preiss's theorem.
-/

open MeasureTheory Filter
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- Positive finite existing m-density almost everywhere implies m-rectifiability. -/
theorem preiss (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) : IsRectifiableMeasure m μ := by
  by_cases hm : m = 0
  · subst m
    exact preiss_zero μ h
  by_cases hmn : m ≤ n
  · have hpos : 0 < m := Nat.pos_of_ne_zero hm
    have hu := ae_tangent_uniform hpos μ h
    have he := ae_exists_flat_tangent hpos hmn μ h
    apply isRectifiableMeasure_of_ae_density_bounds_and_flat_tangents hpos hmn μ
    · filter_upwards [h] with x hx
      exact hx.densities
    · filter_upwards [h, hu, he] with x hx hux hex
      exact all_tangents_flat_of_one hpos hmn μ x hx (fun ν hν ↦ (hux ν hν).1) hex
  · have hz := measure_zero_of_dimension_gt (Nat.lt_of_not_ge hmn) μ h
    subst μ
    exact zero_isRectifiableMeasure

end Preiss
