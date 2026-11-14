module
public import Preiss.Uniform.Defs
public import Preiss.Geometry.FlatMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
open MeasureTheory Metric Set
open scoped BigOperators
namespace Preiss
variable {n m : ℕ}

theorem conical_covariance_eq_projection_of_near_eigenvector
    (hm : 0 < m) (hmn : m ≤ n)
    (e : OrthonormalBasis (Fin n) ℝ (Euclidean n)) (α : Fin n → ℝ)
    (horder : Antitone α) (hα : ∀ i, 0 ≤ α i) (htrace : ∑ i, α i = (m : ℝ))
    (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, (∑ i, α i * (inner ℝ x (e i)) ^ 2) = ‖x‖ ^ 2)
    (i : Fin n) (hi : i.val + 1 = m) (δ : ℝ) (hδ : 0 < δ) (hδm : δ < 1 / (m : ℝ))
    (hnear : ∃ x ∈ S, dist x (e i) < δ) :
    ∀ j, α j = if j.val < m then 1 else 0 := by
  sorry

theorem conical_flatness_gap (hm : 0 < m) (hmn : m ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ν : Measure (Euclidean n)), IsUnitUniform m ν →
      IsConical m ν → (∃ V : Plane m n,
        (∫ z in ball 0 1, (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂ν) ≤ ε) →
      IsFlat m ν := by
  sorry

end Preiss
