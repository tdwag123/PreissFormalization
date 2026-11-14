import Preiss.Tangent.DensityBallLaw
import Preiss.Uniform.Scaling
import Preiss.Tangent.Basic
import Preiss.Geometry.FlatScalar
import FormalizingGMT.MarstrandTheorem

/-! # A common dimensional tangent normalization at a density point

The radius-power density q is fixed before choosing any tangent. This avoids
independently normalizing different tangents when applying a universal flatness gap.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- S08a uses the radius-power density; GMT's diameter density differs by 2^m. -/
theorem dimensionalTangent_ball_constant (hm : 0 < m)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) {q : ℝ} (hq : 0 < q)
    (hd : Tendsto (fun r : ℝ ↦ μ (closedBall x r) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal q)))
    (hu : ∀ ξ, IsTangentMeasure μ ξ x → IsSUniform (m : ℝ) ξ)
    (ν : Measure (Euclidean n)) (hν : IsDimensionalTangent m μ ν x) :
    IsUniformWithConstant m q ν ∧ (0 : Euclidean n) ∈ ν.support := by
  obtain ⟨hball, hzero⟩ := dimensionalTangent_ball_law_at_zero μ x hq hd ν hν
  obtain ⟨_, hreg, _, c, hc, hcball⟩ := hu ν hν.isTangentMeasure
  have heq : ENNReal.ofReal c = ENNReal.ofReal q := by
    simpa only [Real.one_rpow, one_pow, mul_one] using
      (hcball 0 hzero 1 zero_lt_one).symm.trans (hball 1 zero_lt_one)
  have hcq : c = q := by
    have h := congrArg ENNReal.toReal heq
    simpa only [ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal hq.le] using h
  subst c
  refine ⟨⟨hreg, ⟨0, hzero⟩, hq, ?_⟩, hzero⟩
  intro z hz R hR
  simpa only [Real.rpow_natCast] using hcball z hz R hR


/-- S08b: identify the entire normalized tangent family, retaining its common factor. -/
theorem density_normalization_unitUniform (hm : 0 < m)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) {q : ℝ} (hq : 0 < q)
    (hd : Tendsto (fun r : ℝ ↦ μ (closedBall x r) / ENNReal.ofReal (r ^ m))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal q)))
    (hu : ∀ ξ, IsTangentMeasure μ ξ x → IsSUniform (m : ℝ) ξ) :
    (∀ ν, IsDimensionalTangent m ((ENNReal.ofReal q)⁻¹ • μ) ν x ↔
      IsDimensionalTangent m μ (ENNReal.ofReal q • ν) x) ∧
    (∀ ν, IsDimensionalTangent m ((ENNReal.ofReal q)⁻¹ • μ) ν x → IsUnitUniform m ν) ∧
    (∀ ν : Measure (Euclidean n), IsFlat m (ENNReal.ofReal q • ν) ↔ IsFlat m ν) := by
  let C : ℝ≥0∞ := ENNReal.ofReal q
  have hC : 0 < C := ENNReal.ofReal_pos.mpr hq
  have hCtop : C < ∞ := ENNReal.ofReal_lt_top
  have hCinv : 0 < C⁻¹ := ENNReal.inv_pos.mpr hCtop.ne
  have hCinvtop : C⁻¹ < ∞ := lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hC.ne')
  have hequiv (ν : Measure (Euclidean n)) :
      IsDimensionalTangent m (C⁻¹ • μ) ν x ↔ IsDimensionalTangent m μ (C • ν) x := by
    constructor
    · intro hν
      have hh := hν.smul hC hCtop
      simpa only [smul_smul, ENNReal.mul_inv_cancel hC.ne' hCtop.ne, one_smul] using hh
    · intro hν
      have hh := hν.smul hCinv hCinvtop
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC.ne' hCtop.ne, one_smul] using hh
  refine ⟨hequiv, ?_, fun ν => isFlat_smul_iff ν hC hCtop⟩
  intro ν hν
  obtain ⟨hconst, hzero⟩ := dimensionalTangent_ball_constant hm μ x hq hd hu (C • ν)
    ((hequiv ν).mp hν)
  have hscaled := uniformWithConstant_smul (C • ν) hconst (inv_pos.mpr hq)
  have hunit : IsUniformWithConstant m 1 ν := by
    simpa only [C, inv_mul_cancel₀ hq.ne', ENNReal.ofReal_inv_of_pos hq,
      smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hq).ne'
        ENNReal.ofReal_ne_top, one_smul] using hscaled
  rw [measure_support_smul ν hC.ne'] at hzero
  exact (isUnitUniform_iff_constant_one ν).mpr ⟨hunit, hzero⟩


end Preiss
