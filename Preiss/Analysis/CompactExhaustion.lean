module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Compact subsets of measurable increasing exhaustions -/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Preiss

theorem exists_compact_subset_of_ae_mem_iUnion
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (E : Set X) (hE : MeasurableSet E) (S : ℕ → Set X)
    (hS : ∀ i, MeasurableSet (S i)) (hmono : Monotone S)
    (hcover : ∀ᵐ x ∂μ.restrict E, x ∈ ⋃ i, S i) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ C : Set X, IsCompact C ∧ C ⊆ E ∩ S N ∧ μ (E \ C) < ENNReal.ofReal ε := by
  have hzero : μ (E \ ⋃ i, S i) = 0 := by
    have hz : μ ((⋃ i, S i)ᶜ ∩ E) = 0 := by
      rw [← Measure.restrict_apply (MeasurableSet.iUnion hS).compl]
      exact ae_iff.mp hcover
    simpa only [sdiff_eq, inter_comm] using hz
  let u : ℕ → Set X := fun i ↦ E \ S i
  have hu : Antitone u := by
    intro i j hij x hx
    exact ⟨hx.1, fun hi ↦ hx.2 (hmono hij hi)⟩
  have hum (i : ℕ) : NullMeasurableSet (u i) μ := (hE.diff (hS i)).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hum hu ⟨0, measure_ne_top μ _⟩
  have hi : (⋂ i, u i) = E \ ⋃ i, S i := (sdiff_iUnion E S).symm
  rw [hi, hzero] at hlim
  have hhalf : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (half_pos hε)
  obtain ⟨N, hN⟩ := (hlim.eventually_lt_const hhalf).exists
  obtain ⟨C, hCsub, hCcomp, hC⟩ := (hE.inter (hS N)).exists_isCompact_sdiff_lt
    (measure_ne_top μ _) hhalf.ne'
  refine ⟨N, C, hCcomp, hCsub, ?_⟩
  have hsub : E \ C ⊆ (E \ S N) ∪ ((E ∩ S N) \ C) := by
    rintro x ⟨hxE, hxC⟩
    by_cases hxS : x ∈ S N
    · exact Or.inr ⟨⟨hxE, hxS⟩, hxC⟩
    · exact Or.inl ⟨hxE, hxS⟩
  calc
    μ (E \ C) ≤ μ ((E \ S N) ∪ ((E ∩ S N) \ C)) := measure_mono hsub
    _ ≤ μ (E \ S N) + μ ((E ∩ S N) \ C) := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add_of_lt_of_le (measure_ne_top μ _) hN hC.le
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

end Preiss
