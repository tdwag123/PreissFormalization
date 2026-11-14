import Preiss.Rectifiability.Decomposition
import Preiss.Rectifiability.MarstrandMattila.ProjectionNull
import Preiss.Rectifiability.MarstrandMattila.PackingContradiction
import Preiss.Rectifiability.MarstrandMattila.CompactSelection
import Preiss.Rectifiability.MarstrandMattila.HausdorffInputs

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem countablyRectifiable_of_ae_weaklyLinearlyApproximableAt
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    CountablyRectifiable m E := by
  obtain ⟨R, U, hR, hU, _, hRU, hRrect, hUpure⟩ :=
    exists_rectifiable_purelyUnrectifiable_partition E hE hfin
  have hUE : U ⊆ E := by
    intro x hx
    rw [← hRU]
    exact Or.inr hx
  have hUfin : (Measure.hausdorffMeasure (m : ℝ)) U < ∞ :=
    (measure_mono hUE).trans_lt hfin
  have hUw := ae_weaklyLinearlyApproximableAt_subset hE hU hUE hfin hw
  have hUnull : (Measure.hausdorffMeasure (m : ℝ)) U = 0 := by
    by_contra hne
    have hpos : 0 < (Measure.hausdorffMeasure (m : ℝ)) U := pos_iff_ne_zero.mpr hne
    exact false_of_null_projections_and_uniform_weakApproximation hm hmn U hU hpos hUfin
      (ae_upperPowerBoundAt_restrict_hausdorff U hU hUfin) hUw
      (measure_projection_eq_zero_of_purelyUnrectifiable_weakApproximation hm hmn U hU hUfin hUpure hUw)
  apply countablyRectifiable_of_sdiff_null hRrect
  apply measure_mono_null ?_ hUnull
  intro x hx
  have hxRU : x ∈ R ∪ U := by rw [hRU]; exact hx.1
  exact hxRU.resolve_left hx.2

end Preiss
