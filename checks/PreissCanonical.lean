import Preiss.Main

open MeasureTheory
namespace Preiss
variable {m n : ℕ}

/-- Independent verification of the canonical theorem, with its original hypotheses. -/
theorem preiss_canonical_verification (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) : IsRectifiableMeasure m μ :=
  preiss μ h

end Preiss
#print axioms Preiss.preiss
