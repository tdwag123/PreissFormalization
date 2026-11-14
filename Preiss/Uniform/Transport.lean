module

public import Preiss.Uniform.Scaling
public import Preiss.Analysis.ProperMeasureTransport
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Uniform measures under isometric identifications

The embedding is returned as data by dimension reduction and is retained in
all pushforward, support and blow-up identities.
-/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n k : ℕ}

/-- Forward transport preserves the fixed ball constant. -/
theorem uniformWithConstant_map_linearIsometry (L : Euclidean k →ₗᵢ[ℝ] Euclidean n)
    (ν : Measure (Euclidean k)) {q : ℝ} (hν : IsUniformWithConstant m q ν) :
    IsUniformWithConstant m q (ν.map L) := by
  have hL := L.isometry.isClosedEmbedding
  have hs := measure_support_map_of_continuous_of_isClosedMap L L.continuous hL.isClosedMap ν hν.1
  refine ⟨regular_map_of_isProperMap L hL.isProperMap ν hν.1, ?_, hν.2.2.1, ?_⟩
  · rw [hs]
    exact hν.2.1.image L
  · intro y hy r hr
    rw [hs] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Measure.map_apply L.continuous.measurable measurableSet_closedBall,
      L.isometry.preimage_closedBall]
    exact hν.2.2.2 x hx r hr

/-- Forward transport preserves unit uniformity. -/
theorem isUnitUniform_map_linearIsometry (L : Euclidean k →ₗᵢ[ℝ] Euclidean n)
    (ν : Measure (Euclidean k)) (hν : IsUnitUniform m ν) :
    IsUnitUniform m (ν.map L) := by
  apply (isUnitUniform_iff_constant_one _).mpr
  refine ⟨uniformWithConstant_map_linearIsometry L ν
    ((isUnitUniform_iff_constant_one ν).mp hν).1, ?_⟩
  rw [measure_support_map_of_continuous_of_isClosedMap L L.continuous
    L.isometry.isClosedEmbedding.isClosedMap ν hν.1]
  exact ⟨0, hν.2.1, L.map_zero⟩

/-- Pull back a uniform measure concentrated on the isometric image. -/
theorem uniformWithConstant_transport (L : Euclidean k →ₗᵢ[ℝ] Euclidean n)
    (μ : Measure (Euclidean n)) {q : ℝ} (hμ : IsUniformWithConstant m q μ)
    (hsupp : μ.support ⊆ Set.range L) :
    ∃ ν : Measure (Euclidean k), IsUniformWithConstant m q ν ∧ ν.map L = μ ∧
      L '' ν.support = μ.support ∧
      ∀ (x : Euclidean k) (r : ℝ), 0 < r →
        (dimensionalBlowup m ν x r).map L = dimensionalBlowup m μ (L x) r := by
  letI : μ.Regular := hμ.1
  have hL := L.isometry.isClosedEmbedding
  have hme := hL.measurableEmbedding
  let ν := μ.comap L
  letI : IsFiniteMeasureOnCompacts ν :=
    IsFiniteMeasureOnCompacts.comap' μ L.continuous hme
  have hνreg : ν.Regular := inferInstance
  have hmap : ν.map L = μ := by
    change (μ.comap L).map L = μ
    rw [hme.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact measure_mono_null (compl_subset_compl.mpr hsupp)
      (Measure.measure_compl_support_of_regular (μ := μ))
  have hs : L '' ν.support = μ.support := by
    rw [← hmap, measure_support_map_of_continuous_of_isClosedMap L L.continuous
      hL.isClosedMap ν hνreg]
  have hν : IsUniformWithConstant m q ν := by
    refine ⟨hνreg, ?_, hμ.2.2.1, ?_⟩
    · obtain ⟨y, hy⟩ := hμ.2.1
      rw [← hs] at hy
      obtain ⟨x, hx, _⟩ := hy
      exact ⟨x, hx⟩
    · intro x hx r hr
      have hx' : L x ∈ μ.support := hs ▸ mem_image_of_mem L hx
      have hb := hμ.2.2.2 (L x) hx' r hr
      rw [← hmap, Measure.map_apply L.continuous.measurable measurableSet_closedBall,
        L.isometry.preimage_closedBall] at hb
      exact hb
  refine ⟨ν, hν, hmap, hs, ?_⟩
  intro x r hr
  rw [← dimensionalBlowup_map_linearIsometry L ν x r hr, hmap]

/-- A04, generalized to any linear isometric embedding of Euclidean spaces. -/
theorem uniform_hyperplane_transport (L : Euclidean k →ₗᵢ[ℝ] Euclidean n)
    (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ)
    (hsupp : μ.support ⊆ Set.range L) :
    ∃ ν : Measure (Euclidean k), IsUnitUniform m ν ∧ ν.map L = μ ∧
      L '' ν.support = μ.support ∧
      ∀ (x : Euclidean k) (r : ℝ), 0 < r →
        (dimensionalBlowup m ν x r).map L = dimensionalBlowup m μ (L x) r := by
  obtain ⟨ν, hν, hmap, hs, hblow⟩ := uniformWithConstant_transport L μ
    ((isUnitUniform_iff_constant_one μ).mp hμ).1 hsupp
  refine ⟨ν, (isUnitUniform_iff_constant_one ν).mpr ⟨hν, ?_⟩, hmap, hs, hblow⟩
  have h0 : (0 : Euclidean n) ∈ L '' ν.support := by
    rw [hs]
    exact hμ.2.1
  obtain ⟨x, hx, hx0⟩ := h0
  have hx0' : x = 0 := L.injective (by simpa only [map_zero] using hx0)
  simpa only [hx0'] using hx

end Preiss
