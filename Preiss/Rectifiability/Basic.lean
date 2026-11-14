module
public import Preiss.Rectifiability.Defs

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem countablyRectifiable_mono {s t : Set X}
    (ht : CountablyRectifiable m t) (hst : s ⊆ t) : CountablyRectifiable m s := by
  obtain ⟨u, hu, hnull⟩ := ht
  exact ⟨u, hu, measure_mono_null (sdiff_subset_sdiff_left hst) hnull⟩

theorem countablyRectifiable_iUnion (s : ℕ → Set X)
    (hs : ∀ i, CountablyRectifiable m (s i)) : CountablyRectifiable m (⋃ i, s i) := by
  classical
  choose t ht hnull using hs
  choose F hFc hcover using ht
  refine ⟨⋃ i, t i, ⟨⋃ i, F i, Set.countable_iUnion hFc, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨p, hp, hpx⟩ := mem_iUnion₂.mp (hcover i hi)
    exact mem_iUnion₂.mpr ⟨p, mem_iUnion.mpr ⟨i, hp⟩, hpx⟩
  · apply measure_mono_null (t := ⋃ i, s i \ t i) ?_ (measure_iUnion_null hnull)
    rintro x ⟨hx, hxt⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hi, fun h ↦ hxt (mem_iUnion.mpr ⟨i, h⟩)⟩

theorem countablyRectifiable_union {s t : Set X}
    (hs : CountablyRectifiable m s) (ht : CountablyRectifiable m t) :
    CountablyRectifiable m (s ∪ t) := by
  let A : ℕ → Set X := fun i ↦ if i = 0 then s else t
  have hA (i : ℕ) : CountablyRectifiable m (A i) := by
    by_cases hi : i = 0 <;> simp only [A, hi, ite_true, ite_false] <;> assumption
  apply countablyRectifiable_mono (countablyRectifiable_iUnion A hA)
  intro x hx
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨0, by simpa [A] using hx⟩
  · exact mem_iUnion.mpr ⟨1, by simpa [A] using hx⟩

theorem countablyRectifiable_image {s : Set X} (hs : CountablyRectifiable m s)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    CountablyRectifiable m (f '' s) := by
  classical
  obtain ⟨t, ⟨F, hFc, hcover⟩, hnull⟩ := hs
  let g : LipschitzPiece m X → LipschitzPiece m Y := fun p ↦
    { domain := p.domain
      toFun := f ∘ p.toFun
      lipschitz := by
        obtain ⟨L, hL⟩ := p.lipschitz
        exact ⟨K * L, hf.comp hL⟩ }
  refine ⟨f '' t, ⟨g '' F, hFc.image g, ?_⟩, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hpx⟩ := mem_iUnion₂.mp (hcover hx)
    obtain ⟨v, rfl⟩ := hpx
    exact mem_iUnion₂.mpr ⟨g p, ⟨p, hp, rfl⟩, ⟨v, rfl⟩⟩
  · have himage : (Measure.hausdorffMeasure (m : ℝ) : Measure Y) (f '' (s \ t)) = 0 := by
      apply le_antisymm ?_ bot_le
      simpa [hnull] using hf.hausdorffMeasure_image_le (Nat.cast_nonneg m) (s \ t)
    apply measure_mono_null ?_ himage
    rintro y ⟨⟨x, hx, rfl⟩, hyt⟩
    exact ⟨x, ⟨hx, fun hxt ↦ hyt ⟨x, hxt, rfl⟩⟩, rfl⟩

theorem countablyRectifiable_of_sdiff_null {s t : Set X}
    (ht : CountablyRectifiable m t)
    (hnull : (Measure.hausdorffMeasure (m : ℝ) : Measure X) (s \ t) = 0) :
    CountablyRectifiable m s := by
  obtain ⟨u, hu, htu⟩ := ht
  refine ⟨u, hu, measure_mono_null ?_ (measure_union_null hnull htu)⟩
  intro x hx
  by_cases hxt : x ∈ t
  · exact Or.inr ⟨hxt, hx.2⟩
  · exact Or.inl ⟨hx.1, hxt⟩

theorem isRectifiableMeasure_of_countable_restrict (μ : Measure (Euclidean n))
    (S : ℕ → Set (Euclidean n)) (hS : ∀ i, MeasurableSet (S i))
    (hcover : μ (⋃ i, S i)ᶜ = 0)
    (hrect : ∀ i, IsRectifiableMeasure m (μ.restrict (S i))) :
    IsRectifiableMeasure m μ := by
  classical
  have hnull : ∀ A : Set (Euclidean n), (∀ i, μ.restrict (S i) A = 0) → μ A = 0 := by
    intro A hA
    have hi : ∀ i, μ (A ∩ S i) = 0 := by
      intro i
      simpa only [Measure.restrict_apply' (hS i)] using hA i
    apply measure_mono_null ?_ (measure_union_null hcover (measure_iUnion_null hi))
    intro x hx
    by_cases hxs : x ∈ ⋃ i, S i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxs
      exact Or.inr (mem_iUnion.mpr ⟨i, hx, hi⟩)
    · exact Or.inl hxs
  refine ⟨?_, ?_⟩
  · intro A hA
    exact hnull A (fun i ↦ (hrect i).1 hA)
  · choose R hR hRnull using fun i ↦ (hrect i).2
    refine ⟨⋃ i, R i, countablyRectifiable_iUnion R hR, hnull _ ?_⟩
    intro i
    exact measure_mono_null (compl_subset_compl.mpr (subset_iUnion R i)) (hRnull i)

end Preiss
