import Preiss

/-!
# Statement laboratory -- NOT proved mathematics

Every `sorry` here is an explicit blueprint obligation. This module is excluded
from the default `Preiss` target. A successful build only checks the interfaces.
Do not import this module into the reusable library.
-/
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

open scoped CompactlySupported

namespace PreissBlueprint
open Preiss
variable {m n : ℕ}

/-- Image-based rectifiability agrees with countable graph coverage modulo H^m-null sets. -/
theorem countablyRectifiable_iff_lipschitzGraph_cover (s : Set (Euclidean n)) :
    CountablyRectifiable m s ↔ ∃ G : Set (Set (Euclidean n)), G.Countable ∧
      (∀ g ∈ G, IsLipschitzGraph m g) ∧
      (Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean n))
        (s \ ⋃ g ∈ G, g) = 0 := by
  sorry

theorem density_iff_upstream (μ : Measure (Euclidean n)) (x : Euclidean n) :
    HasPositiveFiniteDensityAt m μ x ↔
      x ∈ positiveFiniteDensityExistsSet (m : ℝ) μ := by
  sorry

theorem density_iff_openBall_limit (μ : Measure (Euclidean n)) (x : Euclidean n) :
    HasPositiveFiniteDensityAt m μ x ↔
      ∃ θ : ℝ≥0∞, 0 < θ ∧ θ < ∞ ∧
        Tendsto (fun r : ℝ ↦ μ (ball x r) / ENNReal.ofReal (r ^ m))
          (𝓝[>] 0) (𝓝 θ) := by
  sorry

theorem ae_tangent_uniform (hm : 0 < m) (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x →
      IsSUniform (m : ℝ) ν ∧ (0 : Euclidean n) ∈ ν.support := by
  sorry

theorem tangent_exists (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) (h : HasPositiveFiniteDensitiesAt m μ x) :
    ∃ ν, IsTangentMeasure μ ν x := by
  sorry

/-- Arbitrary scalar tangents are positive scalar multiples of dimensional ones;
they are NOT literally the same set. -/
theorem tangent_iff_dimensional_ray (μ ν : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (h : HasPositiveFiniteDensityAt m μ x) :
    IsTangentMeasure μ ν x ↔ ∃ ξ : Measure (Euclidean n),
      IsDimensionalTangent m μ ξ x ∧
        ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ ν = c • ξ := by
  sorry

theorem tangent_closed (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (x : Euclidean n) (ν : ℕ → Measure (Euclidean n)) (ξ : Measure (Euclidean n))
    (hν : ∀ j, IsTangentMeasure μ (ν j) x) (hξ : ξ.Regular) (hne : ξ ≠ 0)
    (hc : Measure.WeaklyConverges ν ξ) : IsTangentMeasure μ ξ x := by
  sorry

/-- The quantifier over all tangents, centres, and radii lies INSIDE the a.e. binder. -/
theorem ae_recenter_tangent (hm : 0 < m) (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x →
      ∀ y ∈ ν.support, ∀ r : ℝ, 0 < r →
        IsTangentMeasure μ (dimensionalBlowup m ν y r) x := by
  sorry

/-- Corollary 6.5: centres may move. This is a pseudotangent, not necessarily
a tangent at the origin. Keep this distinction in dimension reduction. -/
theorem uniform_has_flat_pseudotangent (hm : 0 < m) (hmn : m ≤ n)
    (ν : Measure (Euclidean n)) (hν : IsSUniform (m : ℝ) ν) :
    ∃ ξ : Measure (Euclidean n), IsFlat m ξ ∧
      ∃ (y : ℕ → Euclidean n) (r : ℕ → ℝ),
        (∀ j, y j ∈ ν.support) ∧ (∀ j, 0 < r j ∧ r j ≤ 1) ∧
          Measure.WeaklyConverges (fun j ↦ dimensionalBlowup m ν (y j) (r j)) ξ := by
  sorry

theorem ae_exists_flat_tangent (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    ∀ᵐ x ∂μ, ∃ ν, IsTangentMeasure μ ν x ∧ IsFlat m ν := by
  sorry

theorem unique_tangent_at_infinity (hm : 0 < m) (hmn : m ≤ n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ ξ : Measure (Euclidean n), IsUnitUniform m ξ ∧
      ∀ ζ, IsTangentAtInfinity m ν ζ ↔ ζ = ξ := by
  sorry

theorem tangent_at_infinity_conical (hm : 0 < m) (hmn : m ≤ n)
    (ν ξ : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hξ : IsTangentAtInfinity m ν ξ) : IsConical m ξ := by
  sorry

/-- Unit normalization is essential: a universal epsilon is false for an
arbitrary positive scalar multiple if the energy is not also normalized. -/
theorem conical_flatness_gap (hm : 0 < m) (hmn : m ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : Measure (Euclidean n),
      IsUnitUniform m ξ → IsConical m ξ →
      (∃ V : Plane m n,
        (∫ z in ball (0 : Euclidean n) 1,
          (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂ξ) ≤ ε) → IsFlat m ξ := by
  sorry

theorem flat_of_flat_at_infinity (hm : 0 < m) (hmn : m ≤ n)
    (ν ξ : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hξ : IsTangentAtInfinity m ν ξ) (hf : IsFlat m ξ) : IsFlat m ν := by
  sorry

theorem flatness_continuous (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ))
    (hφ : ∀ z, 0 ≤ φ z) (ν : ℕ → Measure (Euclidean n))
    (ξ : Measure (Euclidean n)) (hν : ∀ j, (ν j).Regular) (hξ : ξ.Regular)
    (hc : Measure.WeaklyConverges ν ξ) :
    Tendsto (fun j ↦ flatness m φ (ν j)) atTop (𝓝 (flatness m φ ξ)) := by
  sorry

/-- Pointwise Part B. Requires density control and uniformity of ALL tangents;
existence of a flat tangent by itself does not suffice. -/
theorem all_tangents_flat_of_one (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x)
    (hu : ∀ ν, IsTangentMeasure μ ν x → IsSUniform (m : ℝ) ν)
    (hf : ∃ ν, IsTangentMeasure μ ν x ∧ IsFlat m ν) :
    ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν := by
  sorry

theorem absolutelyContinuous_hausdorff_of_upper_density_finite
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, dimensional_upper_density μ.toOuterMeasure (m : ℝ) x < ∞) :
    μ ≪ Measure.hausdorffMeasure (m : ℝ) := by
  sorry

theorem rectifiable_of_weak_approximation (hm : 0 < m) (hmn : m ≤ n)
    (s : Set (Euclidean n)) (hs : MeasurableSet s)
    (hfin : (Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean n)) s < ∞)
    (h : ∀ᵐ x ∂(Measure.hausdorffMeasure (m : ℝ)).restrict s,
      WeaklyLinearlyApproximableAt m s x) : CountablyRectifiable m s := by
  sorry

theorem rectifiable_of_all_tangents_flat (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (hd : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x)
    (hf : ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) :
    IsRectifiableMeasure m μ := by
  sorry

/-- Rectifiability gives a single flat limit under fixed dimensional normalization.
The same plane and coefficient work for EVERY positive sequence tending to zero. -/
theorem rectifiable_has_flat_blowup_limit (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (hrect : IsRectifiableMeasure m μ) :
    ∀ᵐ x ∂μ, ∃ (V : Plane m n) (c : ℝ≥0∞), 0 < c ∧ c < ∞ ∧
      ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
        Measure.WeaklyConverges (fun i => dimensionalBlowup m μ x (r i))
          (c • (Measure.hausdorffMeasure (m : ℝ)).restrict
            (V.1 : Set (Euclidean n))) := by
  sorry

/-- With GMT's arbitrary scalar normalization, the tangent set is a whole ray,
not a singleton. The plane depends on x, but is fixed before quantifying over ν. -/
theorem rectifiable_has_density_and_tangent_plane (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (hrect : IsRectifiableMeasure m μ) :
    ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x ∧ ∃ V : Plane m n,
      ∀ ν, IsTangentMeasure μ ν x ↔ ∃ c : ℝ≥0∞, 0 < c ∧ c < ∞ ∧
        ν = c • (Measure.hausdorffMeasure (m : ℝ)).restrict
          (V.1 : Set (Euclidean n)) := by
  sorry

/-- The density hypothesis here only gives two-sided bounds: no density limit
or common tangent plane is assumed in the right-hand side. -/
theorem rectifiable_iff_density_bounds_and_flat_tangents (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] :
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
      obtain ⟨c, hc0, hctop, heq⟩ := (hV ν).mp hν
      exact ⟨V, c, hc0, hctop, heq⟩
  · rintro ⟨hd, hf⟩
    exact rectifiable_of_all_tangents_flat hm hmn μ hd hf

/-- Density representation uses a sigma-finite carrier, not ambient H^m.
Ambient H^m in R^n is generally NOT sigma-finite when m < n. -/
theorem rectifiable_iff_density_representation (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] :
    IsRectifiableMeasure m μ ↔ ∃ s : Set (Euclidean n),
      MeasurableSet s ∧ CountablyRectifiable m s ∧
      SigmaFinite ((Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean n)).restrict s) ∧
      ∃ f : Euclidean n → ℝ≥0∞, Measurable f ∧
        μ = ((Measure.hausdorffMeasure (m : ℝ)).restrict s).withDensity f := by
  sorry

theorem preiss_zero (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt 0 μ x) : IsRectifiableMeasure 0 μ := by
  sorry

theorem measure_zero_of_dimension_gt (hmn : n < m)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) : μ = 0 := by
  sorry

theorem zero_isRectifiableMeasure : IsRectifiableMeasure m (0 : Measure (Euclidean n)) := by
  sorry

/-- De Lellis 6.1, assembled from the blueprint obligations above.
This theorem still depends on sorryAx through those obligations. -/
theorem preiss (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) : IsRectifiableMeasure m μ := by
  by_cases hm : m = 0
  · subst m
    exact preiss_zero μ h
  by_cases hmn : m ≤ n
  · have hpos : 0 < m := Nat.pos_of_ne_zero hm
    have hu := ae_tangent_uniform hpos μ h
    have he := ae_exists_flat_tangent hpos hmn μ h
    apply rectifiable_of_all_tangents_flat hpos hmn μ
    · filter_upwards [h] with x hx
      exact hx.densities
    · filter_upwards [h, hu, he] with x hx hux hex
      exact all_tangents_flat_of_one hpos hmn μ x hx (fun ν hν ↦ (hux ν hν).1) hex
  · have hz := measure_zero_of_dimension_gt (Nat.lt_of_not_ge hmn) μ h
    subst μ
    exact zero_isRectifiableMeasure

end PreissBlueprint
