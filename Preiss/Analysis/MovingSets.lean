module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Measure bounds for pointwise eventual membership in moving sets -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Preiss
variable {X : Type*} [MeasurableSpace X]

theorem measure_le_of_pointwise_eventually_mem (μ : Measure X)
    (s : ℕ → Set X) (t : Set X) {c : ℝ≥0∞}
    (hbound : ∀ᶠ i in atTop, μ (s i) ≤ c)
    (hpoint : ∀ x ∈ t, ∀ᶠ i in atTop, x ∈ s i) :
    μ t ≤ c := by
  let u : ℕ → Set X := fun N ↦ ⋂ i ≥ N, s i
  have hu : Monotone u := by
    intro N M hNM x hx
    exact mem_iInter₂.mpr fun i hMi ↦ mem_iInter₂.mp hx i (hNM.trans hMi)
  have hsub : t ⊆ ⋃ N, u N := by
    intro x hx
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hpoint x hx)
    exact mem_iUnion.mpr ⟨N, mem_iInter₂.mpr hN⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hbound
  calc
    μ t ≤ μ (⋃ N, u N) := measure_mono hsub
    _ = ⨆ N, μ (u N) := hu.measure_iUnion
    _ ≤ c := by
      apply iSup_le
      intro N
      have hsubN : u N ⊆ s (max N M) := fun x hx ↦
        mem_iInter₂.mp hx (max N M) (le_max_left _ _)
      exact (measure_mono hsubN).trans (hM _ (le_max_right _ _))

theorem le_measure_of_pointwise_eventually_notMem (μ : Measure X) [IsFiniteMeasure μ]
    (s : ℕ → Set X) (t : Set X) {c : ℝ≥0∞}
    (hsm : ∀ i, NullMeasurableSet (s i) μ)
    (hbound : ∀ᶠ i in atTop, c ≤ μ (s i))
    (hpoint : ∀ x ∉ t, ∀ᶠ i in atTop, x ∉ s i) :
    c ≤ μ t := by
  let u : ℕ → Set X := fun N ↦ ⋃ i ≥ N, s i
  have hu : Antitone u := by
    intro N M hNM x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hNM.trans hi, hxi⟩
  have hum (N : ℕ) : NullMeasurableSet (u N) μ :=
    NullMeasurableSet.iUnion fun i ↦ NullMeasurableSet.iUnion fun _ ↦ hsm i
  have hsub : (⋂ N, u N) ⊆ t := by
    intro x hx
    by_contra hxt
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hpoint x hxt)
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (mem_iInter.mp hx N)
    exact hN i hi hxi
  obtain ⟨M, hM⟩ := eventually_atTop.mp hbound
  calc
    c ≤ ⨅ N, μ (u N) := by
      apply le_iInf
      intro N
      have hsubN : s (max N M) ⊆ u N := fun x hx ↦
        mem_iUnion₂.mpr ⟨max N M, le_max_left _ _, hx⟩
      exact (hM _ (le_max_right _ _)).trans (measure_mono hsubN)
    _ = μ (⋂ N, u N) := (hu.measure_iInter hum ⟨0, measure_ne_top μ _⟩).symm
    _ ≤ μ t := measure_mono hsub

end Preiss
