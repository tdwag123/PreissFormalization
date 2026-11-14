import Preiss.Tangent.Normalization
import Preiss.Tangent.Basic
import Preiss.Geometry.FlatScalar

open MeasureTheory
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem exists_flat_dimensionalTangent_of_flat_tangent
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensitiesAt m μ x)
    (ν : Measure (Euclidean n)) (hν : IsTangentMeasure μ ν x) (hflat : IsFlat m ν) :
    ∃ ξ, IsDimensionalTangent m μ ξ x ∧ IsFlat m ξ := by
  obtain ⟨ξ, hξ, c, hc, hctop, rfl⟩ :=
    (tangent_iff_dimensional_ray_of_density_bounds μ ν x hd).mp hν
  exact ⟨ξ, hξ, (isFlat_smul_iff ξ hc hctop).mp hflat⟩

theorem all_tangents_flat_of_dimensionalTangents
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensitiesAt m μ x)
    (hflat : ∀ ξ, IsDimensionalTangent m μ ξ x → IsFlat m ξ) :
    ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν := by
  intro ν hν
  obtain ⟨ξ, hξ, c, hc, hctop, rfl⟩ :=
    (tangent_iff_dimensional_ray_of_density_bounds μ ν x hd).mp hν
  exact (hflat ξ hξ).smul hc hctop

theorem all_dimensionalTangents_flat_of_smul
    (μ : Measure (Euclidean n)) (x : Euclidean n)
    (c : ℝ≥0∞) (hc : 0 < c) (hctop : c < ∞)
    (hflat : ∀ ξ, IsDimensionalTangent m (c • μ) ξ x → IsFlat m ξ) :
    ∀ ν, IsDimensionalTangent m μ ν x → IsFlat m ν := by
  intro ν hν
  exact (isFlat_smul_iff ν hc hctop).mp (hflat (c • ν) (hν.smul hc hctop))

end Preiss
