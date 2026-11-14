import Preiss.Uniform.Defs
import Preiss.Density.Adapters
import FormalizingGMT.MarstrandTheorem

/-! # Adapters to FormalizingGMT uniform measures

These interfaces connect the reusable definitions to the upstream conventions.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem ae_tangent_uniform (hm : 0 < m) (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensityAt m μ x) :
    ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x →
      IsSUniform (m : ℝ) ν ∧ (0 : Euclidean n) ∈ ν.support := by
  obtain ⟨E, hE, hgood⟩ := mattila_14_9 (s := (m : ℝ))
    (by exact_mod_cast hm) μ inferInstance
  have havoid : ∀ᵐ x ∂μ, x ∉ E := measure_eq_zero_iff_ae_notMem.mp hE
  filter_upwards [h, havoid] with x hx hxE
  exact hgood x ⟨(density_iff_upstream μ x).mp hx, hxE⟩

/-- The pure unit ball law agrees with the upstream convention in positive dimension. -/
theorem isUnitUniform_iff (hm : 0 < m) (ν : Measure (Euclidean n)) :
    IsUnitUniform m ν ↔ IsSUniform (m : ℝ) ν ∧
      (0 : Euclidean n) ∈ ν.support ∧ ν (closedBall 0 1) = 1 := by
  constructor
  · intro hν
    have hne : ν ≠ 0 := by
      intro hz
      have h0 := hν.2.1
      simpa [hz] using h0
    refine ⟨⟨by exact_mod_cast hm, hν.1, hne, 1, zero_lt_one, ?_⟩, hν.2.1, ?_⟩
    · intro x hx r hr
      simpa [Real.rpow_natCast] using hν.2.2 x hx r hr
    · simpa using hν.2.2 0 hν.2.1 1 zero_lt_one
  · rintro ⟨hν, h0, hunit⟩
    obtain ⟨_, hreg, _, q, hq, hball⟩ := hν
    have hq1 : ENNReal.ofReal q = 1 := by
      simpa only [Real.one_rpow, mul_one] using
        (hball 0 h0 1 zero_lt_one).symm.trans hunit
    refine ⟨hreg, h0, ?_⟩
    intro x hx r hr
    rw [hball x hx r hr, ENNReal.ofReal_mul hq.le, hq1, one_mul,
      Real.rpow_natCast]

end Preiss
