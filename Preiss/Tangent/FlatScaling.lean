module

public import Preiss.Tangent.Algebra
public import Preiss.Geometry.PlaneMeasure
public import Preiss.Geometry.FlatMeasure
public import Preiss.Analysis.MeasureSupport
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Flat measures under centered blow-ups and isometric embeddings -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem dimensionalBlowup_flatOn (V : Plane m n) (c : ℝ≥0∞)
    (x : Euclidean n) (hx : x ∈ V.1) (r : ℝ) (hr : 0 < r) :
    dimensionalBlowup m (flatOn V c) x r = flatOn V c := by
  let μV : Measure V.1 := Measure.hausdorffMeasure (m : ℝ)
  haveI : Measure.IsAddHaarMeasure μV := by
    dsimp [μV]
    simpa only [V.property] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ V.1 : ℝ) : Measure V.1))
  let v : V.1 := ⟨x, hx⟩
  let f : V.1 → V.1 := fun y => r⁻¹ • (y - v)
  have hf : Measurable f :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  have ht : μV.map (fun y => y - v) = μV := by
    simpa only [sub_eq_add_neg] using Measure.IsAddRightInvariant.map_add_right_eq_self (μ := μV) (-v)
  have hmap : μV.map f = ENNReal.ofReal (r ^ m) • μV := by
    have hsub : Measurable (fun y : V.1 => y - v) :=
      (continuous_id.sub continuous_const).measurable
    change μV.map ((fun y : V.1 => r⁻¹ • y) ∘ (fun y => y - v)) = _
    rw [← Measure.map_map (continuous_const_smul r⁻¹).measurable
      hsub, ht,
      map_addHaar_smul μV (inv_ne_zero hr.ne'), V.property]
    simp only [inv_pow, inv_inv, abs_of_pos (pow_pos hr m)]
  have hval : Measurable (fun y : V.1 => (y : Euclidean n)) := continuous_subtype_val.measurable
  have heq : (fun y : Euclidean n => r⁻¹ • (y - x)) ∘
      (fun y : V.1 => (y : Euclidean n)) =
      (fun y : V.1 => (y : Euclidean n)) ∘ f := rfl
  have hambient : Measurable (fun y : Euclidean n => r⁻¹ • (y - x)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  have hp : ENNReal.ofReal (r ^ m) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'
  rw [flatOn, ← map_hausdorffMeasure_subtype_eq_restrict V,
    dimensionalBlowup_smul _ _ _ hr]
  congr 1
  unfold dimensionalBlowup
  rw [Measure.map_map hambient hval, heq, ← Measure.map_map hval hf,
    hmap, Measure.map_smul _ hval.aemeasurable, smul_smul,
    ENNReal.inv_mul_cancel hp ENNReal.ofReal_ne_top, one_smul]

theorem isFlat_dimensionalBlowup (μ : Measure (Euclidean n)) (hμ : IsFlat m μ)
    (x : Euclidean n) (hx : x ∈ μ.support) (r : ℝ) (hr : 0 < r) :
    IsFlat m (dimensionalBlowup m μ x r) := by
  obtain ⟨V, c, hc, hctop, rfl⟩ := hμ
  rw [measure_support_smul _ hc.ne'] at hx
  have hxV : x ∈ V.1 := by
    have h := (Measure.support_restrict_subset hx).1
    rwa [V.1.closed_of_finiteDimensional.closure_eq] at h
  refine ⟨V, c, hc, hctop, ?_⟩
  exact dimensionalBlowup_flatOn V c x hxV r hr

theorem isFlat_of_dimensionalBlowup_zero (μ : Measure (Euclidean n))
    (r : ℝ) (hr : 0 < r) (h : IsFlat m (dimensionalBlowup m μ 0 r)) :
    IsFlat m μ := by
  obtain ⟨V, c, hc, hctop, heq⟩ := h
  have hcomp : dimensionalBlowup m (dimensionalBlowup m μ 0 r) 0 r⁻¹ = μ := by
    rw [dimensionalBlowup_comp _ _ _ _ _ hr (inv_pos.mpr hr)]
    simp [dimensionalBlowup, hr.ne']
  rw [heq] at hcomp
  change dimensionalBlowup m (flatOn V c) 0 r⁻¹ = μ at hcomp
  rw [dimensionalBlowup_flatOn V c 0 V.1.zero_mem r⁻¹ (inv_pos.mpr hr)] at hcomp
  exact ⟨V, c, hc, hctop, hcomp.symm⟩

theorem isFlat_map_linearIsometry {k : ℕ}
    (L : Euclidean n →ₗᵢ[ℝ] Euclidean k) (μ : Measure (Euclidean n))
    (hμ : IsFlat m μ) : IsFlat m (μ.map L) := by
  obtain ⟨V, c, hc, hctop, rfl⟩ := hμ
  let f : V.1 →ₗ[ℝ] Euclidean k := L.toLinearMap.comp V.1.subtype
  have hf : Function.Injective f := L.injective.comp Subtype.val_injective
  let W : Plane m k := ⟨f.range, by rw [LinearMap.finrank_range_of_inj hf, V.property]⟩
  refine ⟨W, c, hc, hctop, ?_⟩
  rw [Measure.map_smul _ L.continuous.measurable.aemeasurable]
  congr 1
  rw [← map_hausdorffMeasure_subtype_eq_restrict V,
    Measure.map_map L.continuous.measurable continuous_subtype_val.measurable]
  exact (L.isometry.comp isometry_subtype_coe).map_hausdorffMeasure (Or.inl (Nat.cast_nonneg m))

end Preiss
