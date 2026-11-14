import Preiss.Density.RadiusPower
import Preiss.Uniform.GMTAdapters
import Preiss.Uniform.TangentNormalization
import Preiss.Tangent.Recentering
import Preiss.Tangent.FlatFromUniform
import Preiss.Geometry.FlatScalar

/-! # Part A of Preiss's argument: a flat tangent almost everywhere -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {n m : ℕ}

theorem ae_exists_flat_tangent (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    ∀ᵐ x ∂μ, ∃ ν, IsTangentMeasure μ ν x ∧ IsFlat m ν := by
  have hu := ae_tangent_uniform hm μ h
  have hrec := ae_recenter_dimensionalTangent_of_locallyFinite (m := m) μ
  filter_upwards [h, hu, hrec] with x hd hu hr
  obtain ⟨q, hq, hqden⟩ := hd.exists_radiusPowerDensity
  obtain ⟨ν, hν⟩ := (dimensionalTangent_nonempty_compact μ x hd).1
  obtain ⟨hνuniform, hνzero⟩ := dimensionalTangent_ball_constant hm μ x hq hqden
    (fun ξ hξ => (hu ξ hξ).1) ν hν
  obtain ⟨V, hV⟩ := exists_flat_dimensionalTangent_of_uniform_recenter hm hmn μ x ν
    hνuniform hνzero (hr ν hν)
  refine ⟨ENNReal.ofReal q • unitFlat V, hV.isTangentMeasure, ?_⟩
  exact (isFlat_unitFlat V).smul (ENNReal.ofReal_pos.mpr hq) ENNReal.ofReal_lt_top

end Preiss
