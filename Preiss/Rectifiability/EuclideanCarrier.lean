module

public import Preiss.Rectifiability.Basic
public import Preiss.Geometry.LipschitzExtension
public import Preiss.Geometry.PlaneMeasure
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_borel_sigmaFinite_carrier {s : Set (Euclidean n)}
    (hs : CountablyRectifiable m s) :
    ∃ T : Set (Euclidean n), MeasurableSet T ∧ CountablyRectifiable m T ∧
      (Measure.hausdorffMeasure (m : ℝ)) (s \ T) = 0 ∧
      SigmaFinite ((Measure.hausdorffMeasure (m : ℝ)).restrict T) ∧
      ∃ K : ℕ → Set (Euclidean n), T = ⋃ i, K i ∧
        (∀ i, IsCompact (K i)) ∧
        (∀ i, (Measure.hausdorffMeasure (m : ℝ)) (K i) < ∞) := by
  classical
  obtain ⟨t, ⟨F, hFc, hcover⟩, hnull⟩ := hs
  haveI : Countable F := hFc.to_subtype
  have hext (p : F) : ∃ g : Euclidean m → Euclidean n,
      (∃ L : ℝ≥0, LipschitzWith L g) ∧ ∀ x : p.val.domain, g x = p.val.toFun x := by
    obtain ⟨L, hL⟩ := p.val.lipschitz
    exact exists_lipschitz_extension_finiteDimensional p.val.domain p.val.toFun hL
  choose g hg heq using hext
  choose L hL using hg
  let W : F × ℕ → Set (Euclidean n) := fun z ↦ g z.1 '' closedBall 0 (z.2 : ℝ)
  have hWcompact (z : F × ℕ) : IsCompact (W z) :=
    (isCompact_closedBall 0 (z.2 : ℝ)).image (hL z.1).continuous
  have hWfinite (z : F × ℕ) : (Measure.hausdorffMeasure (m : ℝ)) (W z) < ∞ := by
    have hb : (Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean m))
        (closedBall 0 (z.2 : ℝ)) < ∞ := by
      have hb' := (isCompact_closedBall (0 : Euclidean m) (z.2 : ℝ)).measure_lt_top
        (μ := Measure.hausdorffMeasure (Module.finrank ℝ (Euclidean m) : ℝ))
      simpa only [finrank_euclideanSpace_fin] using hb'
    apply lt_of_le_of_lt ((hL z.1).hausdorffMeasure_image_le (Nat.cast_nonneg m) _)
    rw [ENNReal.rpow_natCast]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hb
  let C : Set (Set (Euclidean n)) := insert ∅ (Set.range W)
  have hCc : C.Countable := (Set.countable_range W).insert ∅
  obtain ⟨K, hK⟩ := hCc.exists_eq_range (show C.Nonempty from ⟨∅, Or.inl rfl⟩)
  have hKi (i : ℕ) : K i ∈ C := by rw [hK]; exact Set.mem_range_self i
  have hKcompact (i : ℕ) : IsCompact (K i) := by
    rcases hKi i with he | ⟨z, hz⟩
    · rw [he]; exact isCompact_empty
    · rw [← hz]; exact hWcompact z
  have hKfinite (i : ℕ) : (Measure.hausdorffMeasure (m : ℝ)) (K i) < ∞ := by
    rcases hKi i with he | ⟨z, hz⟩
    · rw [he, measure_empty]; exact ENNReal.zero_lt_top
    · rw [← hz]; exact hWfinite z
  let T := ⋃ i, K i
  have hT : MeasurableSet T := MeasurableSet.iUnion fun i ↦ (hKcompact i).measurableSet
  have hWT (z : F × ℕ) : W z ⊆ T := by
    have hz : W z ∈ Set.range K := by rw [← hK]; exact Or.inr ⟨z, rfl⟩
    obtain ⟨i, hi⟩ := hz
    rw [← hi]
    exact subset_iUnion K i
  have htT : t ⊆ T := by
    intro x hx
    obtain ⟨p, hp, u, hu⟩ := mem_iUnion₂.mp (hcover hx)
    obtain ⟨j, hj⟩ := exists_nat_gt ‖(u : Euclidean m)‖
    apply hWT (⟨p, hp⟩, j)
    refine ⟨u.val, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right] using hj.le
    · exact (heq ⟨p, hp⟩ u).trans hu
  let q : F → LipschitzPiece m (Euclidean n) := fun p ↦
    { domain := Set.univ
      toFun := fun u ↦ g p u.val
      lipschitz := ⟨_, (hL p).comp isometry_subtype_coe.lipschitzWith⟩ }
  have hTcovered : CountablyCoveredByLipschitzPieces m T := by
    refine ⟨Set.range q, Set.countable_range q, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases hKi i with he | ⟨z, hz⟩
    · simpa only [he, Set.mem_empty_iff_false] using hi
    · rw [← hz] at hi
      obtain ⟨u, _, hu⟩ := hi
      exact mem_iUnion₂.mpr ⟨q z.1, ⟨z.1, rfl⟩, ⟨⟨u, mem_univ u⟩, hu⟩⟩
  have hsf : SigmaFinite ((Measure.hausdorffMeasure (m : ℝ)).restrict T) := by
    apply Measure.sigmaFinite_of_countable
      (S := insert Tᶜ (Set.range K)) ((Set.countable_range K).insert Tᶜ)
    · intro A hA
      rcases hA with rfl | ⟨i, rfl⟩
      · rw [Measure.restrict_apply' hT, compl_inter_self, measure_empty]
        exact ENNReal.zero_lt_top
      · exact lt_of_le_of_lt (Measure.le_iff'.1 Measure.restrict_le_self _) (hKfinite i)
    · ext x
      simp only [mem_sUnion, mem_insert_iff, mem_range, mem_univ, iff_true]
      by_cases hx : x ∈ T
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact ⟨K i, Or.inr ⟨i, rfl⟩, hi⟩
      · exact ⟨Tᶜ, Or.inl rfl, hx⟩
  refine ⟨T, hT, ⟨T, hTcovered, by simp⟩, ?_, hsf, K, rfl, hKcompact, hKfinite⟩
  exact measure_mono_null (sdiff_subset_sdiff_right htT) hnull

end Preiss
