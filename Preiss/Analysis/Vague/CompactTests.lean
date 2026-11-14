import Preiss.Geometry.Euclidean
import FormalizingGMT.WeakConvergence.Basic
import Mathlib.Topology.UrysohnsLemma

open MeasureTheory Filter Set
open scoped Topology CompactlySupported
namespace Preiss
variable {n : ℕ}

theorem vague_integral_moving_compact_test
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (f : ℕ → C_c(Euclidean n, ℝ)) (g : C_c(Euclidean n, ℝ))
    (hfK : ∀ i x, x ∉ K → f i x = 0) (hgK : ∀ x, x ∉ K → g x = 0)
    (hfg : ∀ ε > 0, ∀ᶠ i in atTop, ∀ x, |f i x - g x| < ε) :
    Tendsto (fun i => ∫ x, f i x ∂μ i) atTop (𝓝 (∫ x, g x ∂ν)) := by
  obtain ⟨u, huK, hucompact, _, hubounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let cutoff : C_c(Euclidean n, ℝ) := ⟨u, hucompact⟩
  let C : ℝ := (∫ x, cutoff x ∂ν) + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos
    (integral_nonneg (fun x => (hubounds x).1)) zero_lt_one
  have hbound : ∀ᶠ i in atTop, (∫ x, cutoff x ∂μ i) < C :=
    (hlim cutoff).eventually (gt_mem_nhds (lt_add_one _))
  have hdiff : Tendsto (fun i => (∫ x, f i x ∂μ i) - ∫ x, g x ∂μ i)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hδ : 0 < ε / C := div_pos hε hC
    filter_upwards [hfg (ε / C) hδ, hbound] with i hi hBi
    letI : (μ i).Regular := hμ i
    have hdom : ∀ x, ‖f i x - g x‖ ≤ (ε / C) * cutoff x := by
      intro x
      by_cases hx : x ∈ K
      · change |f i x - g x| ≤ (ε / C) * u x
        have hux : u x = 1 := huK hx
        rw [hux, mul_one]
        exact (hi x).le
      · rw [hfK i x hx, hgK x hx, sub_self, norm_zero]
        exact mul_nonneg hδ.le (hubounds x).1
    have hestimate := norm_integral_le_of_norm_le (cutoff.integrable.const_mul (ε / C))
      (ae_of_all (μ i) hdom)
    have hle : |(∫ x, f i x ∂μ i) - ∫ x, g x ∂μ i| ≤
        (ε / C) * ∫ x, cutoff x ∂μ i := by
      rw [← integral_sub (f i).integrable g.integrable]
      simpa only [Real.norm_eq_abs, integral_const_mul] using hestimate
    have hlt : (ε / C) * (∫ x, cutoff x ∂μ i) < ε := by
      calc
        _ < (ε / C) * C := mul_lt_mul_of_pos_left hBi hδ
        _ = ε := div_mul_cancel₀ ε hC.ne'
    simpa only [Real.dist_eq, sub_zero] using hle.trans_lt hlt
  simpa only [zero_add, sub_add_cancel] using hdiff.add (hlim g)

end Preiss
