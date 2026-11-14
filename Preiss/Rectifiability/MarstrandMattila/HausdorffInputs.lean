import Preiss.Rectifiability.WeakApproximation.Restriction
import Preiss.Density.Defs
import Preiss.Density.PowerComparison
import FormalizingGMT.Densities.HausdorffUpperDensityInside
import FormalizingGMT.Densities.HausdorffUpperDensityOutside

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

/-- The finite-Hausdorff upper-density bound, expressed in the pure power-bound
API consumed by the packing theorem. Ambient Hausdorff measure need not be sigma-finite. -/
theorem ae_upperPowerBoundAt_restrict_hausdorff (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : Measure.hausdorffMeasure (m : ℝ) E < ∞) :
    ∀ᵐ x ∂((Measure.hausdorffMeasure (m : ℝ)).restrict E),
      UpperPowerBoundAt m ((Measure.hausdorffMeasure (m : ℝ)).restrict E) x := by
  sorry

theorem lower_density_pos_of_weakApproximation (μ : Measure (Euclidean n)) (x : Euclidean n)
    (h : MeasureWeaklyLinearlyApproximableAt m μ x) :
    0 < dimensional_lower_density μ.toOuterMeasure (m : ℝ) x := by sorry

theorem ae_weaklyLinearlyApproximableAt_subset {E F : Set (Euclidean n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hFE : F ⊆ E)
    (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) (h : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict F), WeaklyLinearlyApproximableAt m F x := by sorry

theorem exists_upper_mass_small_sdiff_point (m n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E G : Set (Euclidean n)),
      MeasurableSet E → MeasurableSet G → G ⊆ E → (Measure.hausdorffMeasure (m : ℝ)) E < ∞ → 0 < (Measure.hausdorffMeasure (m : ℝ)) G →
      ∀ t : ℝ, 0 < t → ∃ (a : Euclidean n) (R : ℝ), a ∈ G ∧ 0 < R ∧
        ∀ r : ℝ, 0 < r → r < R →
          ((Measure.hausdorffMeasure (m : ℝ))).restrict E (ball a r) ≤ ENNReal.ofReal (C * r ^ m) ∧
          (Measure.hausdorffMeasure (m : ℝ)) ((E \ G) ∩ ball a (2 * r)) ≤ ENNReal.ofReal (t * r ^ m) := by sorry

end Preiss
