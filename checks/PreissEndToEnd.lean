import Preiss.Uniform.FlatAtInfinity.TraceLimits
import Preiss.Uniform.ProjectedMixedGaussian
import Preiss.Analysis.GaussianBilinearVectorTrace
import Mathlib.Tactic
import Preiss.Uniform.TraceRigidity
import Preiss.Uniform.RigidityContraction
import Preiss.Analysis.GaussianRigidityBounds
import Preiss.Analysis.OrthogonalTraceSplit
import Preiss.Uniform.FlatAtInfinity.TraceData
import Preiss.Uniform.MomentTrace
import Preiss.Uniform.Classification
import Preiss.Uniform.TangentAtInfinity
import Preiss.Theorem.FirstCrossing
import Preiss.Uniform.TangentNormalization
import Preiss.Tangent.FlatNormalization
import Preiss.Tangent.Compactness
import Preiss.Density.Scalar
import Preiss.Density.RadiusPower
import Preiss.Density.Dimension
import Preiss.Rectifiability.Zero
import Preiss.Uniform.GMTAdapters
import Preiss.Rectifiability.MarstrandMattila.MeasureCriterion
import Preiss.Theorem.PartA
import Preiss.Theorem.PartB

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


end Preiss


/-! Assembly validation only. The remaining total-trace bound is an explicit
parameter; this candidate is not the unconditional flat-at-infinity theorem. -/
open MeasureTheory
namespace Preiss
variable {m n : ℕ}
theorem flat_at_infinity_rigidity_assembly (μ ν : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (hInfinity : IsTangentAtInfinity m μ ν) (hν : IsFlat m ν)
    (hTrace : ∀ (B : MomentCoefficientFamily n), IsMomentExpansion μ B →
      ∀ (V : Plane m n), IsTangentAtInfinity m μ (unitFlat V) →
      ∀ (b : V.1ᗮ), IsFirstMomentNormalVector B V b →
      16*‖b‖^2/((m:ℝ)+2) ≤ bilinearTrace (momentBilinear (B 2 2))) :
    IsFlat m μ := by
  have hνuniform := isUnitUniform_of_tangentAtInfinity μ ν hμ hInfinity
  obtain ⟨V,c,hc,hct,hrepr⟩ := hν
  have hsupp : ν.support = (V.1 : Set (Euclidean n)) := by
    rw [hrepr]
    exact flatOn_support V hc
  have hνeq := unitUniform_eq_flat_of_support_subset_plane hm ν hνuniform V hsupp.subset
  have hV : IsTangentAtInfinity m μ (unitFlat V) := by simpa only [hνeq] using hInfinity
  obtain ⟨B,hB⟩ := exists_gaussianMoment_taylor_coefficients μ hm hμ
  obtain ⟨b,hb⟩ := exists_firstMomentNormalVector μ hm hμ B hB V hV
  have htrace := trace_secondMomentCoefficient_eq_zero μ hm hμ B hB
  have hbound := hTrace B hB V hV b hb
  rw [htrace] at hbound
  have hd : 0 < (m:ℝ)+2 := by positivity
  have hbzero : b = 0 := by
    have h := (div_le_iff₀ hd).mp hbound
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg b, sq_nonneg ‖b‖]
  have hμsupp : μ.support ⊆ (V.1 : Set (Euclidean n)) := by
    intro x hx
    have h := (support_normal_sq_eq_inner μ hm hμ B hB V hV b hb x hx).2.2
    rw [hbzero, norm_zero, mul_zero] at h
    have heq : x = proj V x := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    rw [heq]
    exact (V.1.orthogonalProjectionOnto x).property
  rw [unitUniform_eq_flat_of_support_subset_plane hm μ hμ V hμsupp]
  exact isFlat_unitFlat V
end Preiss


namespace Preiss
open MeasureTheory
variable {m n : ℕ}
theorem flat_of_flat_at_infinity_proved (μ ν : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (hInfinity : IsTangentAtInfinity m μ ν) (hν : IsFlat m ν) : IsFlat m μ := by
  apply flat_at_infinity_rigidity_assembly μ ν hm hμ hInfinity hν
  intro B hB V hV b hb
  obtain ⟨ω,hω,A,hA⟩ := exists_rigidityOmega_and_adjustedForm μ hm hμ B hB V hV b hb
  exact secondMomentCoefficient_trace_lower_bound_proved μ hm hμ B hB V hV b hb ω hω A hA
end Preiss



/-! Assembly check only: the flat-at-infinity rigidity theorem is an explicit hypothesis.
These conditional declarations do not certify the original Part B endpoint. -/

open MeasureTheory Filter Set
open scoped Topology CompactlySupported ENNReal
namespace Preiss
variable {m n : ℕ}
variable (rigidity : ∀ (μ ν : Measure (Euclidean n)), 0 < m → IsUnitUniform m μ →
  IsTangentAtInfinity m μ ν → IsFlat m ν → IsFlat m μ)
include rigidity

theorem exists_dilate_flatness_gt_of_unitUniform_not_flat_of_rigidity
    (hm : 0 < m) (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (ε : ℝ) (hε : IsFlatnessGap m φ ε)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) (hnot : ¬ IsFlat m ν) :
    ∃ R > 0, ε < flatness m φ (dimensionalBlowup m ν 0 R) := by
  by_contra hbad
  push_neg at hbad
  obtain ⟨ψ, hψu, hψ⟩ := exists_unitUniform_tangentAtInfinity ν hν
  have hψflat : IsFlat m ψ := by
    apply hε.2 ψ hψu (tangent_at_infinity_conical hm hmn ν ψ hν hψ)
    obtain ⟨hψreg, hψne, R, hR, hRtop, hlim⟩ := hψ
    apply le_of_tendsto (flatness_continuous hmn φ hφ _ _
      (fun i => regular_dimensionalBlowup ν hν.1 0 (hR i)) hψreg hlim)
    exact Filter.Eventually.of_forall (fun i => hbad (R i) (hR i))
  exact hnot (rigidity ν ψ hm hν hψ hψflat)

theorem exists_first_crossing_sequences_checked_of_rigidity (hm : 0 < m) (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (ε : ℝ) (hε : IsFlatnessGap m φ ε)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x)
    (hu : ∀ ν, IsDimensionalTangent m μ ν x → IsUnitUniform m ν)
    (α ζ : Measure (Euclidean n)) (hα : IsDimensionalTangent m μ α x)
    (hαflat : IsFlat m α) (hζ : IsDimensionalTangent m μ ζ x) (hζnotflat : ¬ IsFlat m ζ) :
    ∃ (ξ : Measure (Euclidean n)) (r σ : ℕ → ℝ), IsUnitUniform m ξ ∧
      IsDimensionalTangent m μ ξ x ∧ FirstCrossingData m μ x φ ε α ξ r σ := by
  obtain ⟨R, hR, hRlarge⟩ := exists_dilate_flatness_gt_of_unitUniform_not_flat_of_rigidity rigidity
    hm hmn φ hφ ε hε ζ (hu ζ hζ) hζnotflat
  exact exists_first_crossing_sequences_of_flatness_gt hmn φ hφ ε hε.1 μ x hd hu
    α (dimensionalBlowup m ζ 0 R) hα hαflat (hζ.dilate hR) hRlarge

theorem all_dimensionalTangents_flat_of_one_of_rigidity
    (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x)
    (hu : ∀ ν, IsDimensionalTangent m μ ν x → IsUnitUniform m ν)
    (hf : ∃ ν, IsDimensionalTangent m μ ν x ∧ IsFlat m ν) :
    ∀ ν, IsDimensionalTangent m μ ν x → IsFlat m ν := by
  classical
  obtain ⟨φ, hφ⟩ := exists_flatnessCutoff n
  obtain ⟨ε, hε⟩ := exists_flatnessGap hm hmn φ hφ
  obtain ⟨α, hα, hαflat⟩ := hf
  intro ζ hζ
  by_contra hζnotflat
  obtain ⟨ξ, r, σ, hξ, hξdim, hcross⟩ := exists_first_crossing_sequences_checked_of_rigidity rigidity
    hm hmn φ hφ ε hε μ x hd hu α ζ hα hαflat hζ hζnotflat
  have hμ : μ.Regular := inferInstance
  have hratio := first_crossing_ratio_tendsto_atTop hmn φ hφ ε hε.1 μ hμ x
    α ξ hαflat hξ r σ hcross
  have hInfinityFlat := (first_crossing_limit_flat_at_infinity hm hmn φ hφ ε hε μ hμ x
    α ξ hξ r σ hcross hratio).2
  obtain ⟨ψ, hψu, hψ⟩ := exists_unitUniform_tangentAtInfinity ξ hξ
  have hflat := rigidity ξ ψ hm hξ hψ (hInfinityFlat ψ hψ)
  have hz := flatness_eq_zero_of_isFlat φ hφ ξ hflat
  have hvalue : flatness m φ ξ = ε := hcross.2.2.2.2.1
  exact hε.1.ne' (hz.symm.trans hvalue).symm

theorem all_tangents_flat_of_one_checked_of_rigidity (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x)
    (hu : ∀ ν, IsTangentMeasure μ ν x → IsSUniform (m : ℝ) ν)
    (hf : ∃ ν, IsTangentMeasure μ ν x ∧ IsFlat m ν) :
    ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν := by
  obtain ⟨q, hq, hqden⟩ := hd.exists_radiusPowerDensity
  let C : ℝ≥0∞ := ENNReal.ofReal q
  have hC : 0 < C := ENNReal.ofReal_pos.mpr hq
  have hCtop : C < ∞ := ENNReal.ofReal_lt_top
  have hCi : 0 < C⁻¹ := ENNReal.inv_pos.mpr hCtop.ne
  have hCitop : C⁻¹ < ∞ := lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hC.ne')
  let μ' := C⁻¹ • μ
  haveI : μ.Regular := inferInstance
  haveI : μ'.Regular := Measure.Regular.smul hCitop.ne
  haveI : IsLocallyFiniteMeasure μ' := inferInstance
  have hd' : HasPositiveFiniteDensityAt m μ' x := hd.smul hCi hCitop
  have hu' : ∀ ν, IsDimensionalTangent m μ' ν x → IsUnitUniform m ν :=
    (density_normalization_unitUniform hm μ x hq hqden hu).2.1
  obtain ⟨ν, hν, hνflat⟩ := hf
  obtain ⟨ξ, hξ, hξflat⟩ := exists_flat_dimensionalTangent_of_flat_tangent μ x hd.densities ν hν hνflat
  have hflat' : ∀ ν, IsDimensionalTangent m μ' ν x → IsFlat m ν :=
    all_dimensionalTangents_flat_of_one_of_rigidity rigidity hm hmn μ' x hd' hu'
      ⟨C⁻¹ • ξ, hξ.smul hCi hCitop, hξflat.smul hCi hCitop⟩
  apply all_tangents_flat_of_dimensionalTangents μ x hd.densities
  exact all_dimensionalTangents_flat_of_smul μ x C⁻¹ hCi hCitop hflat'

end Preiss


open MeasureTheory Filter
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- Positive finite existing m-density almost everywhere implies m-rectifiability. -/
theorem preiss_candidate (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) : IsRectifiableMeasure m μ := by
  by_cases hm : m = 0
  · subst m
    exact preiss_zero μ h
  by_cases hmn : m ≤ n
  · have hpos : 0 < m := Nat.pos_of_ne_zero hm
    have hu := ae_tangent_uniform hpos μ h
    have he := ae_exists_flat_tangent hpos hmn μ h
    apply isRectifiableMeasure_of_ae_density_bounds_and_flat_tangents hpos hmn μ
    · filter_upwards [h] with x hx
      exact hx.densities
    · filter_upwards [h, hu, he] with x hx hux hex
      exact all_tangents_flat_of_one_checked_of_rigidity flat_of_flat_at_infinity_proved hpos hmn μ x hx (fun ν hν ↦ (hux ν hν).1) hex
  · have hz := measure_zero_of_dimension_gt (Nat.lt_of_not_ge hmn) μ h
    subst μ
    exact zero_isRectifiableMeasure

end Preiss

#print axioms Preiss.preiss_candidate
