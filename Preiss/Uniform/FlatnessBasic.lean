module

public import Preiss.Uniform.Flatness
public import Preiss.Geometry.FlatMeasure
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Positivity and vanishing of flatness

These facts require only a nonnegative cutoff. No regularity assumption on the
measure or compactness theorem for the Grassmannian is needed.
-/

@[expose] public section
open MeasureTheory Metric Set
open scoped CompactlySupported ENNReal
namespace Preiss
variable {m n : ℕ}

theorem flatnessEnergy_nonneg (φ : C_c(Euclidean n, ℝ))
    (hφ : ∀ z, 0 ≤ φ z) (μ : Measure (Euclidean n)) (V : Plane m n) :
    0 ≤ flatnessEnergy φ μ V :=
  integral_nonneg (fun z => mul_nonneg (hφ z) (sq_nonneg _))

theorem flatness_nonneg_of_nonneg (m : ℕ) (φ : C_c(Euclidean n, ℝ))
    (hφ : ∀ z, 0 ≤ φ z) (μ : Measure (Euclidean n)) :
    0 ≤ flatness m φ μ := by
  unfold flatness
  by_cases h : (Set.range (flatnessEnergy φ μ : Plane m n → ℝ)).Nonempty
  · apply le_csInf h
    rintro _ ⟨V, rfl⟩
    exact flatnessEnergy_nonneg φ hφ μ V
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

theorem flatnessEnergy_restrict_plane (φ : C_c(Euclidean n, ℝ))
    (V : Plane m n) (c : ℝ≥0∞) :
    flatnessEnergy φ (c • (Measure.hausdorffMeasure (m : ℝ)).restrict
      (V.1 : Set (Euclidean n))) V = 0 := by
  unfold flatnessEnergy
  rw [integral_smul_measure]
  have hzero : (∫ z in (V.1 : Set (Euclidean n)),
      φ z * (infDist z (V.1 : Set (Euclidean n))) ^ 2
        ∂(Measure.hausdorffMeasure (m : ℝ))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem V.1.closed_of_finiteDimensional.measurableSet] with z hz
    simp only [infDist_zero_of_mem hz, zero_pow (by decide : 2 ≠ 0), mul_zero, Pi.zero_apply]
  rw [hzero, smul_zero]

theorem flatness_eq_zero_of_isFlat_of_nonneg (φ : C_c(Euclidean n, ℝ))
    (hφ : ∀ z, 0 ≤ φ z) (μ : Measure (Euclidean n)) (hμ : IsFlat m μ) :
    flatness m φ μ = 0 := by
  obtain ⟨V, c, _, _, rfl⟩ := hμ
  apply le_antisymm ?_ (flatness_nonneg_of_nonneg m φ hφ _)
  have hb : BddBelow (Set.range (flatnessEnergy φ
      (c • (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n))) :
        Plane m n → ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact flatnessEnergy_nonneg φ hφ _ W
  exact (csInf_le hb (Set.mem_range_self V)).trans_eq
    (flatnessEnergy_restrict_plane φ V c)

end Preiss
