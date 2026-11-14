import Preiss.Density.Defs
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Positive finite density bounds under absolute continuity

The Radon–Nikodym derivative is positive and finite almost everywhere for the
absolutely continuous measure. Differentiation along closed balls then transfers
both density bounds, without assuming an existing density limit.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem ae_hasPositiveFiniteDensitiesAt_of_absolutelyContinuous
    (μ ν : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hνμ : ν ≪ μ) (hd : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x) :
    ∀ᵐ x ∂ν, HasPositiveFiniteDensitiesAt m ν x := by
  have hRNpos : ∀ᵐ x ∂ν, 0 < ν.rnDeriv μ x := Measure.rnDeriv_pos hνμ
  have hRNfin : ∀ᵐ x ∂ν, ν.rnDeriv μ x < ∞ :=
    hνμ.ae_le (Measure.rnDeriv_lt_top ν μ)
  filter_upwards [hνμ.ae_le hd, hRNpos, hRNfin,
    hνμ.ae_le (Besicovitch.ae_tendsto_rnDeriv ν μ)] with x hx hpos hfin ht
  obtain ⟨c, hc, hclow⟩ := exists_between hx.1
  obtain ⟨d, hdupp, hdtop⟩ := exists_between hx.2
  obtain ⟨a, ha, haRN⟩ := exists_between hpos
  obtain ⟨b, hbRN, hbtop⟩ := exists_between hfin
  have hrat : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      a * c ≤ dimensional_density_ratio ν.toOuterMeasure (m : ℝ) x r ∧
      dimensional_density_ratio ν.toOuterMeasure (m : ℝ) x r ≤ b * d := by
    filter_upwards [eventually_gt_of_lower_density_gt (m : ℝ) x c hclow,
      eventually_lt_of_upper_density_lt (m : ℝ) x d hdupp,
      ht.eventually (Ioo_mem_nhds haRN hbRN), self_mem_nhdsWithin] with r hrc hrd hrRN hr
    have hμ0 : μ (closedBall x r) ≠ 0 := by
      intro hz
      rw [dimensional_density_ratio_closedBall _ _ _ hr.le] at hrc
      change c < μ (closedBall x r) / ENNReal.ofReal ((2 * r) ^ (m : ℝ)) at hrc
      rw [hz, ENNReal.zero_div] at hrc
      exact (not_lt_of_ge hc.le) hrc
    have hμtop : μ (closedBall x r) ≠ ∞ :=
      (isCompact_closedBall x r).measure_lt_top.ne
    have heq : dimensional_density_ratio ν.toOuterMeasure (m : ℝ) x r =
        (ν (closedBall x r) / μ (closedBall x r)) *
          dimensional_density_ratio μ.toOuterMeasure (m : ℝ) x r := by
      rw [dimensional_density_ratio_closedBall _ _ _ hr.le,
        dimensional_density_ratio_closedBall _ _ _ hr.le]
      change ν (closedBall x r) / ENNReal.ofReal ((2 * r) ^ (m : ℝ)) =
        (ν (closedBall x r) / μ (closedBall x r)) *
          (μ (closedBall x r) / ENNReal.ofReal ((2 * r) ^ (m : ℝ)))
      simp only [div_eq_mul_inv]
      calc
        _ = ν (closedBall x r) *
            ((μ (closedBall x r))⁻¹ * μ (closedBall x r) *
              (ENNReal.ofReal ((2 * r) ^ (m : ℝ)))⁻¹) := by
          rw [ENNReal.inv_mul_cancel hμ0 hμtop, one_mul]
        _ = _ := by ac_rfl
    rw [heq]
    exact ⟨mul_le_mul' hrRN.1.le hrc.le, mul_le_mul' hrRN.2.le hrd.le⟩
  refine ⟨(ENNReal.mul_pos ha.ne' hc.ne').trans_le ?_, ?_⟩
  · exact le_liminf_of_le (h := hrat.mono fun _ h ↦ h.1)
  · exact (limsup_le_of_le (h := hrat.mono fun _ h ↦ h.2)).trans_lt
      (ENNReal.mul_lt_top hbtop hdtop)

end Preiss
