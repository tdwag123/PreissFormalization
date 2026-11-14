import Preiss.Geometry.Euclidean
import Preiss.Analysis.DenseCompactTests
import FormalizingGMT.WeakConvergence.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Detecting vague convergence and measure equality with countably many tests -/

namespace Preiss
open MeasureTheory Filter Set Metric Topology
open scoped CompactlySupported
variable {n : ℕ}

theorem weaklyConverges_iff_denseCompactTests
    (F : DenseCompactTestFamily (Euclidean n))
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular) :
    Measure.WeaklyConverges μ ν ↔ ∀ j,
      Tendsto (fun i => ∫ x, F.tests j x ∂μ i) atTop (𝓝 (∫ x, F.tests j x ∂ν)) := by
  constructor
  · exact fun h j => h (F.tests j)
  · intro h f
    letI : ν.Regular := hν
    obtain ⟨K, hK, hfK, happ⟩ := F.approximation f
    obtain ⟨j₀, hnonneg, hone⟩ := F.cutoffs K hK
    let u := F.tests j₀
    let C := (∫ x, u x ∂ν) + 1
    have hC : 0 < C := add_pos_of_nonneg_of_pos (integral_nonneg hnonneg) zero_lt_one
    have hbound : ∀ᶠ i in atTop, (∫ x, u x ∂μ i) < C :=
      (h j₀).eventually_lt_const (lt_add_one _)
    have hνbound : (∫ x, u x ∂ν) < C := lt_add_one _
    have estimate (ρ : Measure (Euclidean n)) (hρ : ρ.Regular)
        (j : ℕ) (hjK : tsupport (F.tests j) ⊆ K)
        (δ : ℝ) (hδ : 0 ≤ δ) (herr : ∀ x, |F.tests j x - f x| ≤ δ) :
        |(∫ x, F.tests j x ∂ρ) - ∫ x, f x ∂ρ| ≤ δ * ∫ x, u x ∂ρ := by
      letI : ρ.Regular := hρ
      have hdom (x : Euclidean n) : ‖F.tests j x - f x‖ ≤ δ * u x := by
        by_cases hx : x ∈ K
        · change |F.tests j x - f x| ≤ δ * u x
          calc |F.tests j x - f x| ≤ δ := herr x
            _ = δ * 1 := (mul_one _).symm
            _ ≤ δ * u x := mul_le_mul_of_nonneg_left (hone x hx) hδ
        · have ht0 : F.tests j x = 0 :=
            image_eq_zero_of_notMem_tsupport (fun hx' => hx (hjK hx'))
          have hf0 : f x = 0 :=
            image_eq_zero_of_notMem_tsupport (fun hx' => hx (hfK hx'))
          rw [ht0, hf0, sub_self, norm_zero]
          exact mul_nonneg hδ (hnonneg x)
      have he := norm_integral_le_of_norm_le (u.integrable.const_mul δ)
        (ae_of_all ρ hdom)
      rw [← integral_sub (F.tests j).integrable f.integrable]
      simpa only [Real.norm_eq_abs, integral_const_mul] using he
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := ε / (3 * C)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
    have hδC : δ * C = ε / 3 := by
      dsimp [δ]
      field_simp [hC.ne']
    obtain ⟨j, hjK, hj⟩ := happ δ hδ
    have hevent := Metric.tendsto_nhds.mp (h j) (ε / 3) (by positivity)
    filter_upwards [hbound, hevent] with i hi hi'
    have hsource : dist (∫ x, f x ∂μ i) (∫ x, F.tests j x ∂μ i) < ε / 3 := by
      rw [dist_comm, Real.dist_eq]
      apply (estimate (μ i) (hμ i) j hjK δ hδ.le (fun x => (hj x).le)).trans_lt
      calc δ * (∫ x, u x ∂μ i) < δ * C := mul_lt_mul_of_pos_left hi hδ
        _ = ε / 3 := hδC
    have htarget : dist (∫ x, F.tests j x ∂ν) (∫ x, f x ∂ν) < ε / 3 := by
      rw [Real.dist_eq]
      apply (estimate ν hν j hjK δ hδ.le (fun x => (hj x).le)).trans_lt
      calc δ * (∫ x, u x ∂ν) < δ * C := mul_lt_mul_of_pos_left hνbound hδ
        _ = ε / 3 := hδC
    calc dist (∫ x, f x ∂μ i) (∫ x, f x ∂ν)
        ≤ dist (∫ x, f x ∂μ i) (∫ x, F.tests j x ∂μ i) +
          dist (∫ x, F.tests j x ∂μ i) (∫ x, f x ∂ν) := dist_triangle _ _ _
      _ ≤ dist (∫ x, f x ∂μ i) (∫ x, F.tests j x ∂μ i) +
          (dist (∫ x, F.tests j x ∂μ i) (∫ x, F.tests j x ∂ν) +
           dist (∫ x, F.tests j x ∂ν) (∫ x, f x ∂ν)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add hsource (add_lt_add hi' htarget)
      _ = ε := by ring

theorem measure_eq_of_denseCompactTests
    (F : DenseCompactTestFamily (Euclidean n))
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (h : ∀ j, (∫ x, F.tests j x ∂μ) = ∫ x, F.tests j x ∂ν) : μ = ν := by
  letI : μ.Regular := hμ
  letI : ν.Regular := hν
  have hvague := (weaklyConverges_iff_denseCompactTests F (fun _ => μ) ν
    (fun _ => hμ) hν).mpr (fun j => by rw [h j]; exact tendsto_const_nhds)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact tendsto_nhds_unique tendsto_const_nhds (hvague f)

end Preiss
