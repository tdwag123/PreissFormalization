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

/-- A countable cover by Lipschitz graphs gives rectifiability in the sense of
`Defs.lean`. This direction does not use the rank-decomposition lemmas below. -/
theorem countablyRectifiable_of_lipschitzGraph_cover (s : Set (Euclidean n))
    (G : Set (Set (Euclidean n))) (hGc : G.Countable)
    (hG : ∀ Γ ∈ G, IsLipschitzGraph m Γ)
    (hnull : (Measure.hausdorffMeasure (m : ℝ)) (s \ ⋃ Γ ∈ G, Γ) = 0) :
    CountablyRectifiable m s := by
  classical
  by_cases hnon : G.Nonempty
  · obtain ⟨g, hg⟩ := hGc.exists_eq_range hnon
    have hrect (i : ℕ) : CountablyRectifiable m (g i) :=
      countablyRectifiable_subset_graph (hG (g i) (by rw [hg]; exact Set.mem_range_self i))
        Set.Subset.rfl
    have hcover : (⋃ Γ ∈ G, Γ) = ⋃ i, g i := by
      ext x
      constructor
      · intro hx
        obtain ⟨Γ, hΓ, hxΓ⟩ := Set.mem_iUnion₂.mp hx
        rw [hg] at hΓ
        obtain ⟨i, rfl⟩ := hΓ
        exact Set.mem_iUnion.mpr ⟨i, hxΓ⟩
      · intro hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion₂.mpr ⟨g i, by rw [hg]; exact Set.mem_range_self i, hi⟩
    exact countablyRectifiable_of_sdiff_null
      (countablyRectifiable_iUnion g hrect) (by simpa only [hcover] using hnull)
  · have hGempty : G = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro Γ hΓ
      exact hnon ⟨Γ, hΓ⟩
    have hnull' : (Measure.hausdorffMeasure (m : ℝ)) s = 0 := by
      simpa [hGempty] using hnull
    exact ⟨∅, ⟨∅, Set.countable_empty, by simp⟩, by simpa using hnull'⟩

theorem countablyRectifiable_iff_lipschitzGraph_cover (s : Set (Euclidean n)) :
    CountablyRectifiable m s ↔ ∃ G : Set (Set (Euclidean n)), G.Countable ∧
      (∀ Γ ∈ G, IsLipschitzGraph m Γ) ∧ (Measure.hausdorffMeasure (m : ℝ)) (s \ ⋃ Γ ∈ G, Γ) = 0 := by
  constructor
  · sorry
  · rintro ⟨G, hGc, hG, hnull⟩
    exact countablyRectifiable_of_lipschitzGraph_cover s G hGc hG hnull

/-- Null sets for the book-normalized and raw Hausdorff measures agree.
The positive finite value of `ω_m / 2^m` still needs to be connected here. -/
theorem bookHausdorffMeasure_eq_zero_iff (s : Set (Euclidean n)) :
    bookHausdorffMeasure m n s = 0 ↔
      (Measure.hausdorffMeasure (m : ℝ)) s = 0 := by sorry

/-- For Borel sets, the book's definition is equivalent to `CountablyRectifiable`.
The forward implication of `countablyRectifiable_iff_lipschitzGraph_cover` still
depends on the rank-decomposition results above. -/
theorem isBookRectifiable_iff_countablyRectifiable (s : Set (Euclidean n))
    (hs : MeasurableSet s) :
    IsBookRectifiable m s ↔ CountablyRectifiable m s := by
  simpa only [IsBookRectifiable, hs, true_and, bookHausdorffMeasure_eq_zero_iff]
    using (countablyRectifiable_iff_lipschitzGraph_cover s).symm

end Preiss
