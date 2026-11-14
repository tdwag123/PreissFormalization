module
public import Preiss.Uniform.Defs
public import Preiss.Geometry.Planes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section
open MeasureTheory Metric Set
namespace Preiss
variable {n m : ℕ}

theorem dist_support_lt_of_small_gaussian_plane_energy
    (hm : 0 < m) (hmn : m ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (μ : Measure (Euclidean n)), IsUnitUniform m μ →
      ∀ V : Plane m n,
      (∫ z, Real.exp (-‖z‖ ^ 2) * (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ) ≤ η →
      ∀ x ∈ V.1, ‖x‖ ≤ 1 → infDist x μ.support < δ := by
  sorry

end Preiss
