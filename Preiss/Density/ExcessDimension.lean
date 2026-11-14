import Preiss.Uniform.GMTAdapters
import Preiss.Tangent.Existence

/-! # Density dimensions above the ambient dimension

The argument reuses FormalizingGMT's obstruction to uniform measures in excessive dimension.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem measure_zero_of_dimension_gt (hmn : n < m)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) : μ = 0 := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hmn
  have hu := ae_tangent_uniform hm μ h
  have hfalse : ∀ᵐ x ∂μ, False := by
    filter_upwards [h, hu] with x hx hux
    obtain ⟨ν, hν⟩ := tangent_exists μ x hx.densities
    exact SUniformAux.not_isSUniform_of_lt (s := (m : ℝ))
      (by exact_mod_cast hmn) ν (hux ν hν).1
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.setOf_true] using hfalse

end Preiss
