import Preiss.Tangent.Defs
import Preiss.Density.Defs
import FormalizingGMT.TangentMeasures.Basic

/-! # Compactness

Fixed-dimensional subsequence compactness under pointwise density bounds.

Statements are formalization obligations. Proofs are intentionally pending.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_dimensional_tangent_subseq_of_density_bounds
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (h : HasPositiveFiniteDensitiesAt m μ x) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Euclidean n)), StrictMono φ ∧ ν.Regular ∧ ν ≠ 0 ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m μ x (r (φ i))) ν ∧
      IsTangentMeasure μ ν x := by sorry

theorem dimensionalTangent_closed
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (ν : ℕ → Measure (Euclidean n)) (ξ : Measure (Euclidean n))
    (hν : ∀ i, IsDimensionalTangent m μ (ν i) x)
    (hlim : Measure.WeaklyConverges ν ξ) (hξ : ξ.Regular) (hξ0 : ξ ≠ 0) :
    IsDimensionalTangent m μ ξ x := by
  sorry

theorem tangent_closed
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (ν : ℕ → Measure (Euclidean n)) (ξ : Measure (Euclidean n))
    (hν : ∀ i, IsTangentMeasure μ (ν i) x)
    (hlim : Measure.WeaklyConverges ν ξ) (hξ : ξ.Regular) (hξ0 : ξ ≠ 0) :
    IsTangentMeasure μ ξ x := by
  sorry

theorem dimensionalTangent_dilate (μ ν : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hν : IsDimensionalTangent m μ ν x) (r : ℝ) (hr : 0 < r) :
    IsDimensionalTangent m μ (dimensionalBlowup m ν 0 r) x := by
  sorry

theorem dimensionalTangent_nonempty_compact
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x) :
    (∃ ν, IsDimensionalTangent m μ ν x) ∧
    ∀ ν : ℕ → Measure (Euclidean n),
      (∀ i, IsDimensionalTangent m μ (ν i) x) →
      ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧
        IsDimensionalTangent m μ ξ x ∧ Measure.WeaklyConverges (ν ∘ φ) ξ := by
  sorry

end Preiss
