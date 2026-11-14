import Preiss.Uniform.FlatAtInfinity.TraceLimits
import Preiss.Uniform.ProjectedMixedGaussian
import Preiss.Analysis.GaussianBilinearVectorTrace
import Mathlib.Tactic
import Preiss.Uniform.TraceRigidity
import Preiss.Uniform.RigidityContraction
import Preiss.Analysis.GaussianRigidityBounds
import Preiss.Analysis.OrthogonalTraceSplit
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem integral_rigidityOmega_eq_zero_draft
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω) :
    (∫ v : V.1, ω v v ∂stdGaussian V.1) = 0 := by
  classical
  let e := stdOrthonormalBasis ℝ V.1
  have hB21 (u : V.1) : B 2 1 ![(u : Euclidean n),(u : Euclidean n)] = inner ℝ u u := by
    have h := evenMomentCoefficient_eq_projection_norm μ hm hμ B hB V hV 1 (by decide) u
    have hu : ![(u : Euclidean n),(u : Euclidean n)] = (fun _ : Fin 2 => (u : Euclidean n)) := by
      funext i
      fin_cases i <;> rfl
    rw [hu]
    simpa [proj, real_inner_self_eq_norm_sq] using h
  apply ext_inner_right ℝ
  intro w
  rw [inner_zero_left, gaussian_integral_bilinear_eq_basis_sum e ω, sum_inner]
  have hlim := tendsto_finset_sum Finset.univ (fun i _ => show
      Tendsto (fun s => (8*s / gaussianMass μ s) *
        ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z (e i : Euclidean n))^2 *
          inner ℝ (z-(b : Euclidean n)) (w : Euclidean n) ∂μ)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (ω (e i) (e i)) w)) from by
    rw [hω.2]
    simpa only [hB21, Submodule.coe_inner] using
      mixed_gaussian_limit_eq_omega μ hm hμ B hB V hV b hb (e i) w)
  have hz : Tendsto (fun s => ∑ i, (8*s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z (e i : Euclidean n))^2 *
        inner ℝ (z-(b : Euclidean n)) (w : Euclidean n) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (contracted_gaussian_limit_eq_zero μ hm hμ B hB V hV b hb w).const_mul 8
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (sum_mixed_gaussian_eq_projected μ hm hμ V.1 e b w s hs).symm
  exact tendsto_nhds_unique hlim hz

theorem trace_tangent_eq_integral_adjustedForm_draft
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
    (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A) :
    bilinearTrace (restrictBilinear (momentBilinear (B 2 2)) V.1) =
      ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  let D := restrictBilinear (momentBilinear (B 2 2)) V.1
  apply gaussian_integral_bilinear_eq_trace_of_mean_zero_correction D A ω
    (integral_rigidityOmega_eq_zero_draft μ hm hμ B hB V hV b hb ω hω) b
  intro u v
  rw [hA.2]
  congr 1
  change B 2 2 ![(u : Euclidean n),(v : Euclidean n)] =
    B 2 2 (Fin.cons (u : Euclidean n) (fun _ => (v : Euclidean n)))
  congr 1
  ext i
  fin_cases i <;> rfl

theorem integral_inner_sq_mul_omega_draft
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω) (y : V.1) (w : V.1ᗮ) :
    (∫ v : V.1, (inner ℝ y v)^2 * inner ℝ (ω v v) w ∂stdGaussian V.1) =
      2 * inner ℝ (ω y y) w := by
  exact gaussian_integral_inner_sq_mul_bilinear_of_mean_zero ω
    (integral_rigidityOmega_eq_zero_draft μ hm hμ B hB V hV b hb ω hω) y w

theorem integral_adjustedForm_sq_le_proved
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
    (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A) :
    (∫ v : V.1, (A v v)^2 ∂stdGaussian V.1) ≤
      -8 * ‖b‖^2 * ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  have hmean := rigidityOmega_contraction_of_mean_zero_and_error_limit μ hm hμ B hB V hV b hb ω hω A
    (integral_rigidityOmega_eq_zero_draft μ hm hμ B hB V hV b hb ω hω)
    (adjustedForm_gaussian_error_tendsto_zero μ hm hμ B hB V hV b hb ω hω A hA)
  exact (gaussian_quadratic_bounds_of_mean_square_identity A hA.1 ω
    (by rw [V.2]; exact hm) (‖b‖^2) (sq_nonneg _)
    (adjustedForm_sq_le_norm_omega_sq μ hm hμ B hB V hV b hb ω hω A hA) hmean).1

theorem integral_adjustedForm_lower_bound_proved
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
    (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A) :
    -8 * (m : ℝ) * ‖b‖^2 / ((m : ℝ)+2) ≤ ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  have h := gaussian_bilinear_integral_lower_bound_of_square_upper A hA.1
    (by rw [V.2]; exact hm) (‖b‖^2) (sq_nonneg _)
    (integral_adjustedForm_sq_le_proved μ hm hμ B hB V hV b hb ω hω A hA)
  simpa only [V.2] using h

theorem secondMomentCoefficient_trace_lower_bound_proved
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
    (A : RigidityAdjustedForm V) (hA : IsRigidityAdjustedForm B V b ω A) :
    16*‖b‖^2/((m:ℝ)+2) ≤ bilinearTrace (momentBilinear (B 2 2)) := by
  have hnormal := trace_secondMomentCoefficient_normal_eq μ hm hμ B hB V hV b hb
  have htangent := trace_tangent_eq_integral_adjustedForm_draft μ hm hμ B hB V hV b hb ω hω A hA
  have hlower := integral_adjustedForm_lower_bound_proved μ hm hμ B hB V hV b hb ω hω A hA
  rw [bilinearTrace_eq_restrict_add_orthogonal _ V.1, hnormal, htangent]
  have hd : 0 < (m:ℝ)+2 := by positivity
  apply (div_le_iff₀ hd).mpr
  have h := (div_le_iff₀ hd).mp hlower
  nlinarith

#print axioms integral_adjustedForm_sq_le_proved
#print axioms integral_adjustedForm_lower_bound_proved
#print axioms secondMomentCoefficient_trace_lower_bound_proved

end Preiss
