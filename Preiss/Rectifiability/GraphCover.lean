module

public import Preiss.Rectifiability.Cones
public import Preiss.Rectifiability.EuclideanCarrier
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem hausdorffMeasure_image_eq_zero_of_lipschitz_null
    (A : Set (Euclidean m)) (f : A → Euclidean n) {K : ℝ≥0}
    (hf : LipschitzWith K f) (hnull : volume A = 0) :
    (Measure.hausdorffMeasure (m : ℝ)) (Set.range f) = 0 := by sorry

theorem hausdorffMeasure_image_rank_lt_eq_zero
    (f : Euclidean m → Euclidean n) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : Set (Euclidean m))
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hrank : ∀ x ∈ s,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) < m) :
    (Measure.hausdorffMeasure (m : ℝ)) (f '' s) = 0 := by sorry

theorem exists_countable_graph_cover_fullRank_locus
    (f : Euclidean m → Euclidean n) {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : Set (Euclidean m))
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hrank : ∀ x ∈ s,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = m) :
    ∃ G : Set (Set (Euclidean n)), G.Countable ∧
      (∀ Γ ∈ G, IsLipschitzGraph m Γ) ∧ f '' s ⊆ ⋃ Γ ∈ G, Γ := by sorry

theorem countablyRectifiable_iff_lipschitzGraph_cover (s : Set (Euclidean n)) :
    CountablyRectifiable m s ↔ ∃ G : Set (Set (Euclidean n)), G.Countable ∧
      (∀ Γ ∈ G, IsLipschitzGraph m Γ) ∧ (Measure.hausdorffMeasure (m : ℝ)) (s \ ⋃ Γ ∈ G, Γ) = 0 := by sorry

end Preiss
