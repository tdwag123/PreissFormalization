import Preiss.Tangent.Basic
import Preiss.Density.Defs
import FormalizingGMT.MarstrandTheorem
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Dimensional blow-up subsequences under local power bounds -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem exists_dimensional_tangent_subseq_of_ball_bounds
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    {p q R₀ : ℝ} (hp : 0 < p) (hq : 0 < q) (hR₀ : 0 < R₀)
    (hup : ∀ t, 0 < t → t < R₀ → μ (closedBall x t) ≤ ENNReal.ofReal (q * t ^ m))
    (hlo : ∀ t, 0 < t → t < R₀ → ENNReal.ofReal (p * t ^ m) ≤ μ (closedBall x t))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Euclidean n)), StrictMono φ ∧ ν.Regular ∧ ν ≠ 0 ∧
      Measure.WeaklyConverges (fun i => dimensionalBlowup m μ x (r (φ i))) ν ∧
      IsTangentMeasure μ ν x := by
  classical
  let τ (i : ℕ) := dimensionalBlowup m μ x (r i)
  have hreg (i : ℕ) : (τ i).Regular := regular_dimensionalBlowup μ inferInstance x (hr i)
  have hball (i : ℕ) (R : ℝ) : τ i (closedBall 0 R) =
      (ENNReal.ofReal ((r i) ^ m))⁻¹ * μ (closedBall x (r i * R)) := by
    change ((ENNReal.ofReal ((r i) ^ m))⁻¹ • μ.map (blowUpMap x (r i))) _ = _
    rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_closedBall μ x (hr i)]
  have hcancel (i : ℕ) (R b : ℝ) :
      (ENNReal.ofReal ((r i) ^ m))⁻¹ * ENNReal.ofReal (b * (r i * R) ^ m) =
        ENNReal.ofReal (b * R ^ m) := by
    rw [show b * (r i * R) ^ m = (r i) ^ m * (b * R ^ m) by rw [mul_pow]; ring,
      ENNReal.ofReal_mul (pow_nonneg (hr i).le m), ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (pow_pos (hr i) m)).ne'
        ENNReal.ofReal_ne_top, one_mul]
  have hevent (R : ℝ) (hR : 0 < R) :
      ∀ᶠ i in atTop, τ i (closedBall 0 R) ≤ ENNReal.ofReal (q * R ^ m) := by
    have hsmall : ∀ᶠ i in atTop, r i * R < R₀ :=
      (by simpa using hr0.mul_const R : Tendsto (fun i => r i * R) atTop (𝓝 0)).eventually_lt_const hR₀
    filter_upwards [hsmall] with i hi
    rw [hball, ← hcancel i R q]
    gcongr
    exact hup _ (mul_pos (hr i) hR) hi
  have hbound : ∀ K : Set (Euclidean n), IsCompact K →
      ∃ C : ℝ≥0, ∀ i, τ i K ≤ C := by
    intro K hK
    obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Euclidean n)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hevent R hR)
    have hfin (i : ℕ) : τ i K ≠ ∞ := by
      haveI := hreg i
      exact hK.measure_lt_top.ne
    let B : ℝ≥0 := (Finset.range N).sup (fun i => (τ i K).toNNReal)
    refine ⟨max B (q * R ^ m).toNNReal, fun i => ?_⟩
    by_cases hi : i < N
    · have hb : (τ i K).toNNReal ≤ B :=
        Finset.le_sup (f := fun i => (τ i K).toNNReal) (Finset.mem_range.mpr hi)
      calc τ i K = ((τ i K).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal (hfin i)).symm
        _ ≤ (B : ℝ≥0∞) := by exact_mod_cast hb
        _ ≤ ((max B (q * R ^ m).toNNReal : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_max_left B (q * R ^ m).toNNReal
    · exact (measure_mono hKR).trans ((hN i (le_of_not_gt hi)).trans (by
        change ((q * R ^ m).toNNReal : ℝ≥0∞) ≤ _
        exact_mod_cast le_max_right B (q * R ^ m).toNNReal))
  obtain ⟨φ, ν, hφ, hν, hlim⟩ := exists_vaguelyConvergent_subseq_of_compact_bounded τ hbound
  have hνne : ν ≠ 0 := by
    have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν
      (fun i => hreg (φ i)) hν).mp hlim
    have hloev : ∀ᶠ i in atTop, ENNReal.ofReal p ≤ τ (φ i) (closedBall 0 1) := by
      filter_upwards [(hr0.comp hφ.tendsto_atTop).eventually_lt_const hR₀] with i hi
      rw [hball, mul_one]
      calc ENNReal.ofReal p = (ENNReal.ofReal ((r (φ i)) ^ m))⁻¹ *
          ENNReal.ofReal (p * (r (φ i)) ^ m) := by simpa using (hcancel (φ i) 1 p).symm
        _ ≤ _ := by gcongr; exact hlo _ (hr (φ i)) hi
    have hmass : ENNReal.ofReal p ≤ ν (closedBall 0 1) :=
      (le_limsup_of_frequently_le hloev.frequently).trans (hb.1 _ (isCompact_closedBall 0 1))
    intro hzero
    exact (ENNReal.ofReal_pos.mpr hp).not_ge (by simpa [hzero] using hmass)
  have hdim : IsDimensionalTangent m μ ν x :=
    ⟨hν, hνne, r ∘ φ, fun i => hr (φ i), hr0.comp hφ.tendsto_atTop, hlim⟩
  exact ⟨φ, ν, hφ, hν, hνne, hlim, hdim.isTangentMeasure⟩

theorem exists_dimensional_tangent_subseq_of_density_bounds
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (h : HasPositiveFiniteDensitiesAt m μ x) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Euclidean n)), StrictMono φ ∧ ν.Regular ∧ ν ≠ 0 ∧
      Measure.WeaklyConverges (fun i => dimensionalBlowup m μ x (r (φ i))) ν ∧
      IsTangentMeasure μ ν x := by
  obtain ⟨p, q, R, hp, hq, hR, hup, hlo⟩ := SUniformAux.ball_bounds_of_mem
    (show x ∈ positiveFiniteDensitySet (m : ℝ) μ from
      ⟨h.1, lower_le_upper_density (m : ℝ) x, h.2⟩)
  apply exists_dimensional_tangent_subseq_of_ball_bounds μ x hp hq hR
    (by simpa only [Real.rpow_natCast] using hup)
    (by simpa only [Real.rpow_natCast] using hlo) r hr hr0

end Preiss
