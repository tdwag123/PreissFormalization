module

public import Preiss.Rectifiability.EuclideanCarrier
public import Preiss.Rectifiability.GraphCover
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem rectifiable_iff_density_representation (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] :
    IsRectifiableMeasure m μ ↔ ∃ (S : Set (Euclidean n)) (f : Euclidean n → ℝ≥0∞),
      MeasurableSet S ∧ CountablyRectifiable m S ∧
      SigmaFinite ((Measure.hausdorffMeasure (m : ℝ)).restrict S) ∧
      Measurable f ∧ μ = ((Measure.hausdorffMeasure (m : ℝ)).restrict S).withDensity f := by
  constructor
  · rintro ⟨hμ, s, hs, hsc⟩
    obtain ⟨S, hSmeas, hSrect, hsS, hSfinite, _⟩ := exists_borel_sigmaFinite_carrier hs
    let H : Measure (Euclidean n) := (Measure.hausdorffMeasure (m : ℝ)).restrict S
    haveI : SigmaFinite H := hSfinite
    have hSc : μ Sᶜ = 0 := by
      apply measure_mono_null (t := sᶜ ∪ (s \ S)) ?_ (measure_union_null hsc (hμ hsS))
      intro x hx
      by_cases hxs : x ∈ s
      · exact Or.inr ⟨hxs, hx⟩
      · exact Or.inl hxs
    have hμH : μ ≪ H := by
      intro A hA
      have hAS : μ (A ∩ S) = 0 := by
        apply hμ
        simpa only [H, Measure.restrict_apply' hSmeas] using hA
      apply measure_mono_null (t := (A ∩ S) ∪ Sᶜ) ?_ (measure_union_null hAS hSc)
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨hx, hxS⟩
      · exact Or.inr hxS
    exact ⟨S, μ.rnDeriv H, hSmeas, hSrect, hSfinite,
      Measure.measurable_rnDeriv μ H, (Measure.withDensity_rnDeriv_eq μ H hμH).symm⟩
  · rintro ⟨S, f, hSmeas, hSrect, _, _, rfl⟩
    refine ⟨(withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict,
      S, hSrect, ?_⟩
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply' hSmeas, compl_inter_self, measure_empty]

/-- The book's measure definition, with an extended nonnegative Borel density.
The set is Borel and satisfies the book's graph-cover definition. -/
def IsBookRectifiableMeasure (m : ℕ) (μ : Measure (Euclidean n)) : Prop :=
  ∃ (S : Set (Euclidean n)) (f : Euclidean n → ℝ≥0∞),
    IsBookRectifiable m S ∧ Measurable f ∧
      μ = ((Measure.hausdorffMeasure (m : ℝ)).restrict S).withDensity f

/-- The book's measure formulation agrees with `IsRectifiableMeasure` for locally
finite measures. This uses the graph-cover equivalence in `GraphCover.lean`. -/
theorem isBookRectifiableMeasure_iff (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] :
    IsBookRectifiableMeasure m μ ↔ IsRectifiableMeasure m μ := by
  constructor
  · rintro ⟨S, f, hS, _, rfl⟩
    have hSmeas : MeasurableSet S := hS.1
    refine ⟨(withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict,
      S, (isBookRectifiable_iff_countablyRectifiable S hSmeas).mp hS, ?_⟩
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply' hSmeas, compl_inter_self, measure_empty]
  · intro hμ
    obtain ⟨S, f, hSmeas, hSrect, _, hf, hEq⟩ :=
      (rectifiable_iff_density_representation μ).mp hμ
    exact ⟨S, f, (isBookRectifiable_iff_countablyRectifiable S hSmeas).mpr hSrect,
      hf, hEq⟩

end Preiss
