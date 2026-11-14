import Preiss.Uniform.Scaling
import FormalizingGMT.MarstrandTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.NormNum

/-! # Uniqueness of full-dimensional uniform measures with fixed ball constant -/

open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem uniformWithConstant_eq_of_fullDimension (hm : 0 < m)
    (μ ν : Measure (Euclidean m)) {q : ℝ}
    (hμ : IsUniformWithConstant m q μ) (hν : IsUniformWithConstant m q ν) : μ = ν := by
  have huniform (ρ : Measure (Euclidean m)) (hρ : IsUniformWithConstant m q ρ) :
      IsSUniform (m : ℝ) ρ := by
    refine ⟨by exact_mod_cast hm, hρ.1, ?_, q, hρ.2.2.1, ?_⟩
    · intro hzero
      obtain ⟨x, hx⟩ := hρ.2.1
      simpa [hzero] using hx
    · intro x hx r hr
      simpa only [Real.rpow_natCast] using hρ.2.2.2 x hx r hr
  obtain ⟨K, hK, hKtop, hμeq⟩ := mattila_14_11 μ (huniform μ hμ)
  obtain ⟨L, hL, hLtop, hνeq⟩ := mattila_14_11 ν (huniform ν hν)
  have hμ0 : (0 : Euclidean m) ∈ μ.support := by
    rw [hμeq, measure_support_smul _ hK.ne', Measure.support_eq_univ]
    exact mem_univ _
  have hν0 : (0 : Euclidean m) ∈ ν.support := by
    rw [hνeq, measure_support_smul _ hL.ne', Measure.support_eq_univ]
    exact mem_univ _
  have hKm : K * volume (closedBall (0 : Euclidean m) 1) = ENNReal.ofReal q := by
    simpa only [hμeq, Measure.smul_apply, smul_eq_mul, one_pow, mul_one] using
      hμ.2.2.2 0 hμ0 1 zero_lt_one
  have hLm : L * volume (closedBall (0 : Euclidean m) 1) = ENNReal.ofReal q := by
    simpa only [hνeq, Measure.smul_apply, smul_eq_mul, one_pow, mul_one] using
      hν.2.2.2 0 hν0 1 zero_lt_one
  have hB0 : volume (closedBall (0 : Euclidean m) 1) ≠ 0 :=
    (measure_closedBall_pos volume (0 : Euclidean m) zero_lt_one).ne'
  have hBtop : volume (closedBall (0 : Euclidean m) 1) ≠ ∞ :=
    (isCompact_closedBall (0 : Euclidean m) 1).measure_lt_top.ne
  have hKL : K = L := (ENNReal.mul_left_inj hB0 hBtop).mp (hKm.trans hLm.symm)
  rw [hμeq, hνeq, hKL]


end Preiss
