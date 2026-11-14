module
public import Preiss.Geometry.PlaneMeasure

/-! # Reflection invariance of flat measures -/

@[expose] public section
open MeasureTheory
namespace Preiss
variable {m n : ℕ}

theorem flatOn_map_neg (V : Plane m n) (c : ℝ≥0∞) :
    (flatOn V c).map (fun z => -z) = flatOn V c := by
  let e : Euclidean n ≃ᵢ Euclidean n :=
    (LinearIsometryEquiv.neg ℝ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n).toIsometryEquiv
  have hH : (Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean n)).map
      (fun z => -z) = Measure.hausdorffMeasure (m : ℝ) :=
    e.map_hausdorffMeasure (m : ℝ)
  have hV : (fun z : Euclidean n => -z) ⁻¹' (V.1 : Set (Euclidean n)) = V.1 := by
    ext z
    simp only [Set.mem_preimage, SetLike.mem_coe, neg_mem_iff]
  have hrestrict : ((Measure.hausdorffMeasure (m : ℝ)).restrict
      (V.1 : Set (Euclidean n))).map (fun z => -z) =
      (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n)) := by
    ext S hS
    rw [Measure.map_apply measurable_neg hS,
      Measure.restrict_apply (measurable_neg hS), Measure.restrict_apply hS]
    have h := congrArg (fun μ : Measure (Euclidean n) => μ (S ∩ V.1)) hH
    rw [Measure.map_apply measurable_neg (hS.inter V.1.closed_of_finiteDimensional.measurableSet)] at h
    simpa only [Set.preimage_inter, hV] using h
  rw [flatOn, Measure.map_smul _ measurable_neg.aemeasurable, hrestrict]

theorem unitFlat_map_neg (V : Plane m n) :
    (unitFlat V).map (fun z => -z) = unitFlat V := by
  rw [unitFlat, Measure.map_smul _ measurable_neg.aemeasurable, flatOn_map_neg]

end Preiss
