module
public import Preiss.Tangent.Blowup
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace Preiss
variable {n m : ℕ}

theorem dimensionalBlowup_comp (μ : Measure (Euclidean n)) (a b : Euclidean n)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    dimensionalBlowup m (dimensionalBlowup m μ a r) b s =
      dimensionalBlowup m μ (a + r • b) (r * s) := by
  have hrmap : Measurable (fun y : Euclidean n => r⁻¹ • (y - a)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  have hsmap : Measurable (fun y : Euclidean n => s⁻¹ • (y - b)) :=
    ((continuous_id.sub continuous_const).const_smul s⁻¹).measurable
  have hcomp : (fun y : Euclidean n => s⁻¹ • (y - b)) ∘
      (fun y : Euclidean n => r⁻¹ • (y - a)) =
      (fun y : Euclidean n => (r * s)⁻¹ • (y - (a + r • b))) := by
    funext y
    simp [Function.comp_def, smul_sub, smul_add, smul_smul, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm, hr.ne', sub_add_eq_sub_sub]
  have hcoeff : (ENNReal.ofReal (s ^ m))⁻¹ * (ENNReal.ofReal (r ^ m))⁻¹ =
      (ENNReal.ofReal ((r * s) ^ m))⁻¹ := by
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le m),
      ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
    exact mul_comm _ _
  unfold dimensionalBlowup
  rw [Measure.map_smul _ hsmap.aemeasurable, Measure.map_map hsmap hrmap,
    smul_smul, hcomp, hcoeff]

theorem dimensionalBlowup_smul (μ : Measure (Euclidean n)) (a : Euclidean n)
    (r : ℝ) (hr : 0 < r) (c : ℝ≥0∞) :
    dimensionalBlowup m (c • μ) a r = c • dimensionalBlowup m μ a r := by
  have hmap : Measurable (fun y : Euclidean n => r⁻¹ • (y - a)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  unfold dimensionalBlowup
  rw [Measure.map_smul _ hmap.aemeasurable, smul_comm]

theorem dimensionalBlowup_map_linearIsometry {k : ℕ}
    (L : Euclidean n →ₗᵢ[ℝ] Euclidean k) (μ : Measure (Euclidean n))
    (a : Euclidean n) (r : ℝ) (hr : 0 < r) :
    dimensionalBlowup m (μ.map L) (L a) r = (dimensionalBlowup m μ a r).map L := by
  have hn : Measurable (fun y : Euclidean n => r⁻¹ • (y - a)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  have hk : Measurable (fun y : Euclidean k => r⁻¹ • (y - L a)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  have hcomp : (fun y : Euclidean k => r⁻¹ • (y - L a)) ∘ L =
      L ∘ (fun y : Euclidean n => r⁻¹ • (y - a)) := by
    funext y
    simp only [Function.comp_apply, map_smul, map_sub]
  unfold dimensionalBlowup
  rw [Measure.map_smul _ L.continuous.measurable.aemeasurable,
    Measure.map_map hk L.continuous.measurable,
    Measure.map_map L.continuous.measurable hn, hcomp]

end Preiss
