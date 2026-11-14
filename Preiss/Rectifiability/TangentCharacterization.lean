import Preiss.Rectifiability.TangentNecessity
import Preiss.Rectifiability.MarstrandMattila.MeasureCriterion

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem rectifiable_iff_density_bounds_and_flat_tangents
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] :
    IsRectifiableMeasure m μ ↔
      (∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x) ∧
      (∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) := by
  constructor
  · intro hrect
    have h := rectifiable_has_density_and_tangent_plane hm hmn μ hrect
    constructor
    · filter_upwards [h] with x hx
      exact hx.1.densities
    · filter_upwards [h] with x hx
      obtain ⟨V, hV⟩ := hx.2
      intro ν hν
      obtain ⟨c, hc, hctop, heq⟩ := (hV ν).mp hν
      exact ⟨V, c, hc, hctop, heq⟩
  · rintro ⟨hd, ht⟩
    exact isRectifiableMeasure_of_ae_density_bounds_and_flat_tangents hm hmn μ hd ht

/-- Rectifiability is equivalent to a positive finite density and one common
tangent plane at almost every point. General tangent measures include every
positive finite multiple of Hausdorff measure on that plane. -/
theorem rectifiable_iff_density_and_tangent_plane
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] :
    IsRectifiableMeasure m μ ↔
      ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x ∧ ∃ V : Plane m n,
        ∀ ν : Measure (Euclidean n), IsTangentMeasure μ ν x ↔
          ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ ν = flatOn V c := by
  constructor
  · exact rectifiable_has_density_and_tangent_plane hm hmn μ
  · intro h
    apply (rectifiable_iff_density_bounds_and_flat_tangents hm hmn μ).mpr
    constructor
    · filter_upwards [h] with x hx
      exact hx.1.densities
    · filter_upwards [h] with x hx
      obtain ⟨V, hV⟩ := hx.2
      intro ν hν
      obtain ⟨c, hc, hctop, heq⟩ := (hV ν).mp hν
      exact ⟨V, c, hc, hctop, heq⟩

end Preiss
