import Preiss.Theorem.FirstCrossing
import Preiss.Uniform.FlatAtInfinity.Rigidity
import Preiss.Uniform.TangentAtInfinity
import Preiss.Uniform.TangentNormalization
import Preiss.Tangent.FlatNormalization
import Preiss.Tangent.Compactness
import Preiss.Density.Scalar
import Preiss.Density.RadiusPower
import Mathlib.Tactic


/-! # Part B of Preiss: one flat tangent forces all tangents to be flat -/
open MeasureTheory Filter Set
open scoped Topology CompactlySupported ENNReal
namespace Preiss
variable {n m : ℕ}

theorem all_dimensionalTangents_flat_of_one
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
  obtain ⟨ξ, r, σ, hξ, hξdim, hcross⟩ := exists_first_crossing_sequences
    hm hmn φ hφ ε hε μ x hd hu α ζ hα hαflat hζ hζnotflat
  have hμ : μ.Regular := inferInstance
  have hratio := first_crossing_ratio_tendsto_atTop hmn φ hφ ε hε.1 μ hμ x
    α ξ hαflat hξ r σ hcross
  have hInfinityFlat := (first_crossing_limit_flat_at_infinity hm hmn φ hφ ε hε μ hμ x
    α ξ hξ r σ hcross hratio).2
  obtain ⟨ψ, hψu, hψ⟩ := exists_unitUniform_tangentAtInfinity ξ hξ
  have hflat := flat_of_flat_at_infinity ξ ψ hm hξ hψ (hInfinityFlat ψ hψ)
  have hz := flatness_eq_zero_of_isFlat φ hφ ξ hflat
  have hvalue : flatness m φ ξ = ε := hcross.2.2.2.2.1
  exact hε.1.ne' (hz.symm.trans hvalue).symm

theorem all_tangents_flat_of_one (hm : 0 < m) (hmn : m ≤ n)
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
    all_dimensionalTangents_flat_of_one hm hmn μ' x hd' hu'
      ⟨C⁻¹ • ξ, hξ.smul hCi hCitop, hξflat.smul hCi hCitop⟩
  apply all_tangents_flat_of_dimensionalTangents μ x hd.densities
  exact all_dimensionalTangents_flat_of_smul μ x C⁻¹ hCi hCitop hflat'

end Preiss
