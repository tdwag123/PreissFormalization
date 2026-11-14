import Preiss.Analysis.QuadraticBoundedOffset
import Preiss.Uniform.RigidityError
import Preiss.Analysis.Vague.Support
import Preiss.Uniform.Scaling
import Mathlib.Tactic
namespace Preiss
open MeasureTheory Filter Set
open scoped Topology
variable {n m : ℕ}
theorem adjustedForm_sq_le_of_rigidityError_linear_growth
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (A : RigidityAdjustedForm V)
    (hlinear : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ μ.support,
      |rigidityError V b ω A z| ≤ C*(1+‖z‖)) (v : V.1) :
    (A v v)^2 ≤ ‖b‖^2 * ‖ω v v‖^2 := by
  obtain ⟨C,hC,hbound⟩ := hlinear
  have hVorig := hV
  obtain ⟨hreg,_,r,hr,hrinf,hlim⟩ := hV
  have hν (i : ℕ) := isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i)
  have hv : (v : Euclidean n) ∈ (unitFlat V).support := by
    rw [unitFlat_support]; exact v.property
  obtain ⟨y,hmem,hy⟩ := exists_support_sequence_of_vague _ _
    (fun i => (hν i).1) hreg hlim v hv
  have hrescale : ∀ᶠ i in atTop, r i • y i ∈ μ.support := by
    filter_upwards [hmem] with i hi
    rw [dimensionalBlowup_support μ 0 (hr i)] at hi
    obtain ⟨z,hz,hzy⟩ := hi
    rw [← hzy]
    simpa only [sub_zero, smul_smul, mul_inv_cancel₀ (hr i).ne', one_smul] using hz
  let u := fun i => V.1.orthogonalProjectionOnto (y i)
  let q := fun i => r i • y i - proj V (r i • y i) - (b : Euclidean n)
  have hu : Tendsto u atTop (𝓝 v) := by
    simpa only [u, Function.comp_def, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using
      (V.1.orthogonalProjectionOnto.continuous.tendsto (v : Euclidean n)).comp hy
  have hq : ∀ᶠ i in atTop, ‖q i‖ ≤ ‖b‖ := by
    filter_upwards [hrescale] with i hi
    exact (support_normal_sq_eq_inner μ hm hμ B hB V
      hVorig b hb (r i • y i) hi).2.1.le
  have hrinv : Tendsto (fun i => (r i)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hrinf
  have herr : Tendsto (fun i => A (u i) (u i) + inner ℝ (ω (u i) (u i) : Euclidean n) (q i))
      atTop (𝓝 0) := by
    have hscale (i : ℕ) :
        A (u i) (u i) + inner ℝ (ω (u i) (u i) : Euclidean n) (q i) =
          (r i)⁻¹^2 * rigidityError V b ω A (r i • y i) := by
      simp only [rigidityError, map_smul, ContinuousLinearMap.smul_apply,
        Submodule.coe_smul, smul_smul, smul_eq_mul, inner_smul_left, conj_trivial, u, q]
      field_simp [(hr i).ne']
      <;> ring
    have hlimbound : Tendsto (fun i => C*((r i)⁻¹^2+(r i)⁻¹*‖y i‖)) atTop (𝓝 0) := by
      simpa using ((hrinv.pow 2).add (hrinv.mul hy.norm)).const_mul C
    apply squeeze_zero_norm' _ hlimbound
    filter_upwards [hrescale] with i hi
    rw [hscale, norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    calc
      (r i)⁻¹^2 * |rigidityError V b ω A (r i • y i)| ≤
          (r i)⁻¹^2 * (C*(1+‖r i • y i‖)) :=
        mul_le_mul_of_nonneg_left (hbound _ hi) (sq_nonneg _)
      _ = C*((r i)⁻¹^2+(r i)⁻¹*‖y i‖) := by
        rw [norm_smul, Real.norm_of_nonneg (hr i).le]
        field_simp [(hr i).ne']
        <;> ring
  let ω' : V.1 →L[ℝ] V.1 →L[ℝ] Euclidean n :=
    ((ContinuousLinearMap.compL ℝ V.1 V.1ᗮ (Euclidean n)) V.1ᗮ.subtypeL).comp ω
  exact quadratic_square_bound_of_bounded_offsets A ω'
    u v hu q ‖b‖ (norm_nonneg b) hq herr
end Preiss

