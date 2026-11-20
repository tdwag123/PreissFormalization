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

/-- Definition 4.1 of De Lellis: a locally finite measure represented by a
nonnegative Borel density against his normalized Hausdorff measure restricted
to a Borel set covered, modulo null sets, by countably many Lipschitz graphs. -/
def IsBookRectifiableMeasure (m : ℕ) (μ : Measure (Euclidean n)) : Prop :=
  IsLocallyFiniteMeasure μ ∧
    ∃ (S : Set (Euclidean n)) (f : Euclidean n → ℝ≥0),
      IsBookRectifiable m S ∧ Measurable f ∧
        μ = ((bookHausdorffMeasure m n).restrict S).withDensity
          (fun x => (f x : ℝ≥0∞))

/-- The paper-facing definition should agree with `IsRectifiableMeasure` for
locally finite measures. The graph-cover, Hausdorff-normalization, and
finite-density correspondences are still unfinished. -/
theorem isBookRectifiableMeasure_iff (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] :
    IsBookRectifiableMeasure m μ ↔ IsRectifiableMeasure m μ := by sorry

end Preiss
