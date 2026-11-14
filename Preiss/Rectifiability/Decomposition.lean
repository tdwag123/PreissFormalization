module

public import Preiss.Rectifiability.PurelyUnrectifiable
public import Preiss.Rectifiability.EuclideanCarrier
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Order.IsLUB

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_rectifiable_purelyUnrectifiable_partition (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) :
    ∃ R U : Set (Euclidean n), MeasurableSet R ∧ MeasurableSet U ∧
      Disjoint R U ∧ R ∪ U = E ∧ CountablyRectifiable m R ∧ PurelyUnrectifiable m U := by
  classical
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (m : ℝ)
  let C : Set (Set (Euclidean n)) := {R | MeasurableSet R ∧ R ⊆ E ∧ CountablyRectifiable m R}
  have hempty : (∅ : Set (Euclidean n)) ∈ C := by
    refine ⟨MeasurableSet.empty, empty_subset _, ∅, ⟨∅, countable_empty, by simp⟩, by simp⟩
  let S : Set ℝ≥0∞ := H '' C
  have hSne : S.Nonempty := ⟨H ∅, ∅, hempty, rfl⟩
  have hSbdd : BddAbove S := ⟨H E, by rintro _ ⟨R, hR, rfl⟩; exact measure_mono hR.2.1⟩
  obtain ⟨v, _, hvlim, hvS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose R hRC hv using hvS
  let R₀ := ⋃ i, R i
  have hRmeas : MeasurableSet R₀ := MeasurableSet.iUnion fun i ↦ (hRC i).1
  have hRE : R₀ ⊆ E := iUnion_subset fun i ↦ (hRC i).2.1
  have hRrect : CountablyRectifiable m R₀ :=
    countablyRectifiable_iUnion R fun i ↦ (hRC i).2.2
  have hRfin : H R₀ < ∞ := (measure_mono hRE).trans_lt hfin
  have hsup : sSup S ≤ H R₀ := by
    apply le_of_tendsto' hvlim
    intro i
    rw [← hv i]
    exact measure_mono (subset_iUnion R i)
  have hmax (T : Set (Euclidean n)) (hT : T ∈ C) : H T ≤ H R₀ :=
    (le_csSup hSbdd ⟨T, hT, rfl⟩).trans hsup
  refine ⟨R₀, E \ R₀, hRmeas, hE.diff hRmeas, ?_, ?_, hRrect, ?_⟩
  · exact disjoint_sdiff_self_right
  · apply subset_antisymm (union_subset hRE sdiff_subset)
    intro x hx
    by_cases hxR : x ∈ R₀
    · exact Or.inl hxR
    · exact Or.inr ⟨hx, hxR⟩
  · intro Q hQ
    obtain ⟨T, hTmeas, hTrect, hQnull, _, _⟩ := exists_borel_sigmaFinite_carrier hQ
    let A := (E \ R₀) ∩ T
    have hAmeas : MeasurableSet A := (hE.diff hRmeas).inter hTmeas
    have hArect : CountablyRectifiable m A :=
      countablyRectifiable_mono hTrect inter_subset_right
    have hdis : Disjoint R₀ A := by
      apply Set.disjoint_left.mpr
      intro x hx hxA
      exact hxA.1.2 hx
    have hsum : H R₀ + H A ≤ H R₀ := by
      rw [← measure_union hdis hAmeas]
      apply hmax
      refine ⟨hRmeas.union hAmeas, ?_, countablyRectifiable_union hRrect hArect⟩
      exact union_subset hRE (fun _ hx ↦ hx.1.1)
    have hAzero : H A = 0 := by
      apply le_antisymm ?_ bot_le
      change H A ≤ 0
      apply (add_le_add_iff_right_of_ne_top hRfin.ne).mp
      simpa only [add_zero] using hsum
    apply measure_mono_null (t := A ∪ (Q \ T)) ?_ (measure_union_null hAzero hQnull)
    rintro x ⟨hxE, hxQ⟩
    by_cases hxT : x ∈ T
    · exact Or.inl ⟨hxE, hxT⟩
    · exact Or.inr ⟨hxQ, hxT⟩

theorem rectifiable_pure_partition_unique {E R U R' U' : Set (Euclidean n)}
    (hunion : R ∪ U = E) (hunion' : R' ∪ U' = E)
    (hR : CountablyRectifiable m R) (hR' : CountablyRectifiable m R')
    (hU : PurelyUnrectifiable m U) (hU' : PurelyUnrectifiable m U') :
    Measure.hausdorffMeasure (m : ℝ) (R \ R') = 0 ∧
      Measure.hausdorffMeasure (m : ℝ) (R' \ R) = 0 ∧
      Measure.hausdorffMeasure (m : ℝ) (U \ U') = 0 ∧
      Measure.hausdorffMeasure (m : ℝ) (U' \ U) = 0 := by
  refine ⟨measure_mono_null ?_ (hU' R hR),
    measure_mono_null ?_ (hU R' hR'),
    measure_mono_null ?_ (hU R' hR'),
    measure_mono_null ?_ (hU' R hR)⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R' ∪ U' := by
      rw [hunion', ← hunion]
      exact Or.inl hx
    exact ⟨hxE.resolve_left hx', hx⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R ∪ U := by
      rw [hunion, ← hunion']
      exact Or.inl hx
    exact ⟨hxE.resolve_left hx', hx⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R' ∪ U' := by
      rw [hunion', ← hunion]
      exact Or.inr hx
    exact ⟨hx, hxE.resolve_right hx'⟩
  · rintro x ⟨hx, hx'⟩
    have hxE : x ∈ R ∪ U := by
      rw [hunion, ← hunion']
      exact Or.inr hx
    exact ⟨hx, hxE.resolve_right hx'⟩

end Preiss
