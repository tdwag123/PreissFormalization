module

public import Preiss.Rectifiability.Cones
public import Preiss.Rectifiability.EuclideanCarrier
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem hausdorffMeasure_image_eq_zero_of_lipschitz_null
    (A : Set (Euclidean m)) (f : A → Euclidean n) {K : ℝ≥0}
    (hf : LipschitzWith K f) (hnull : volume A = 0) :
    (Measure.hausdorffMeasure (m : ℝ)) (Set.range f) = 0 := by
  have hA : (Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean m)) A = 0 := by
    have hA' := Measure.absolutelyContinuous_isAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ (Euclidean m) : ℝ)) volume hnull
    simpa only [finrank_euclideanSpace_fin] using hA'
  obtain ⟨F, ⟨L, hL⟩, heq⟩ := exists_lipschitz_extension_finiteDimensional A f hf
  have hsub : Set.range f ⊆ F '' A := by
    rintro x ⟨u, rfl⟩
    exact ⟨u.val, u.property, heq u⟩
  apply measure_mono_null hsub
  apply le_antisymm ?_ bot_le
  change (Measure.hausdorffMeasure (m : ℝ)) (F '' A) ≤ 0
  simpa only [hA, mul_zero] using hL.hausdorffMeasure_image_le (Nat.cast_nonneg m) A

theorem hausdorffMeasure_image_rank_lt_eq_zero
    (f : Euclidean m → Euclidean n) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : Set (Euclidean m))
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hrank : ∀ x ∈ s,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) < m) :
    (Measure.hausdorffMeasure (m : ℝ)) (f '' s) = 0 := by sorry

theorem exists_countable_graph_cover_fullRank_locus
    (f : Euclidean m → Euclidean n) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : Set (Euclidean m))
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hrank : ∀ x ∈ s,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = m) :
    ∃ G : Set (Set (Euclidean n)), G.Countable ∧
      (∀ Γ ∈ G, IsLipschitzGraph m Γ) ∧ f '' s ⊆ ⋃ Γ ∈ G, Γ := by sorry

theorem countablyRectifiable_iff_lipschitzGraph_cover (s : Set (Euclidean n)) :
    CountablyRectifiable m s ↔ ∃ G : Set (Set (Euclidean n)), G.Countable ∧
      (∀ Γ ∈ G, IsLipschitzGraph m Γ) ∧ (Measure.hausdorffMeasure (m : ℝ)) (s \ ⋃ Γ ∈ G, Γ) = 0 := by sorry

end Preiss
