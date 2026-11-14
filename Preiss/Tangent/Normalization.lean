import Preiss.Tangent.Extraction
import Preiss.Analysis.Vague.ScalarLimits

/-! # General tangent measures are rays of dimensional tangents

Positive lower and finite upper density suffice; existence of the density limit is unnecessary.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem tangent_iff_dimensional_ray_of_ball_bounds
    (μ ν : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    {p q R : ℝ} (hp : 0 < p) (hq : 0 < q) (hR : 0 < R)
    (hup : ∀ t, 0 < t → t < R → μ (closedBall x t) ≤ ENNReal.ofReal (q * t ^ m))
    (hlo : ∀ t, 0 < t → t < R → ENNReal.ofReal (p * t ^ m) ≤ μ (closedBall x t)) :
    IsTangentMeasure μ ν x ↔ ∃ ξ : Measure (Euclidean n),
      IsDimensionalTangent m μ ξ x ∧
        ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ ν = c • ξ := by
  constructor
  · rintro ⟨hνreg, hνne, r, c, hr, hc, hctop, hr0, hlim⟩
    obtain ⟨φ, ξ, hφ, hξreg, hξne, hξlim, _⟩ :=
      exists_dimensional_tangent_subseq_of_ball_bounds μ x hp hq hR hup hlo r hr hr0
    have heq (i : ℕ) :
        (c (φ i) * ENNReal.ofReal ((r (φ i)) ^ m)) • dimensionalBlowup m μ x (r (φ i)) =
          c (φ i) • μ.map (blowUpMap x (r (φ i))) := by
      unfold dimensionalBlowup
      rw [smul_smul, mul_assoc, ENNReal.mul_inv_cancel
        (ENNReal.ofReal_pos.mpr (pow_pos (hr (φ i)) m)).ne' ENNReal.ofReal_ne_top, mul_one]
      rfl
    have hscaled : Measure.WeaklyConverges
        (fun i => (c (φ i) * ENNReal.ofReal ((r (φ i)) ^ m)) •
          dimensionalBlowup m μ x (r (φ i))) ν := by
      simp only [heq]
      exact hlim.comp hφ.tendsto_atTop
    obtain ⟨a, ha, hatop, heqa⟩ := exists_pos_smul_of_vague_and_scaled_vague
      (fun i => dimensionalBlowup m μ x (r (φ i))) ξ ν hξreg hνreg hξne hνne
      (fun i => c (φ i) * ENNReal.ofReal ((r (φ i)) ^ m)) hξlim hscaled
    exact ⟨ξ, ⟨hξreg, hξne, r ∘ φ, fun i => hr (φ i), hr0.comp hφ.tendsto_atTop, hξlim⟩,
      a, ha, hatop, heqa⟩
  · rintro ⟨ξ, hξ, c, hc, hctop, rfl⟩
    exact isTangentMeasure_smul hξ.isTangentMeasure hc hctop

theorem tangent_iff_dimensional_ray_of_density_bounds
    (μ ν : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (h : HasPositiveFiniteDensitiesAt m μ x) :
    IsTangentMeasure μ ν x ↔ ∃ ξ : Measure (Euclidean n),
      IsDimensionalTangent m μ ξ x ∧
        ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ ν = c • ξ := by
  obtain ⟨p, q, R, hp, hq, hR, hup, hlo⟩ := SUniformAux.ball_bounds_of_mem
    (show x ∈ positiveFiniteDensitySet (m : ℝ) μ from
      ⟨h.1, lower_le_upper_density (m : ℝ) x, h.2⟩)
  exact tangent_iff_dimensional_ray_of_ball_bounds μ ν x hp hq hR
    (by simpa only [Real.rpow_natCast] using hup)
    (by simpa only [Real.rpow_natCast] using hlo)

theorem tangent_iff_dimensional_ray (μ ν : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (h : HasPositiveFiniteDensityAt m μ x) :
    IsTangentMeasure μ ν x ↔ ∃ ξ : Measure (Euclidean n),
      IsDimensionalTangent m μ ξ x ∧
        ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ ν = c • ξ := by
  exact tangent_iff_dimensional_ray_of_density_bounds μ ν x h.densities

end Preiss
