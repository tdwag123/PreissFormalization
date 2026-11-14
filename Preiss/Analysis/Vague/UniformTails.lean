import Preiss.Geometry.Euclidean
import FormalizingGMT.WeakConvergence.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic

open MeasureTheory Metric Set Filter
open scoped Topology CompactlySupported
namespace Preiss

theorem norm_integral_sub_cutoff_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f χ : X → ℝ) (K : Set X)
    (hf : Integrable f μ) (hc : Integrable (fun x => χ x * f x) μ)
    (hone : ∀ x ∈ K, χ x = 1) (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) :
    ‖(∫ x, f x ∂μ) - ∫ x, χ x * f x ∂μ‖ ≤ ∫ x in Kᶜ, ‖f x‖ ∂μ := by
  rw [← integral_sub hf hc]
  have heq : (∫ x in Kᶜ, f x - χ x * f x ∂μ) = ∫ x, f x - χ x * f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hxK : x ∈ K := by simpa only [mem_compl_iff, not_not] using hx
      simp [hone x hxK])
  rw [← heq]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hf.sub hc).norm.integrableOn hf.norm.integrableOn
  apply Eventually.of_forall
  intro x
  calc
    ‖f x - χ x * f x‖ = ‖1 - χ x‖ * ‖f x‖ := by rw [← norm_mul]; congr 1; ring
    _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
      linarith [(hχ x).1]) (norm_nonneg _)
    _ = ‖f x‖ := one_mul _

theorem vague_integral_of_uniform_norm_tails {n : ℕ}
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (f : Euclidean n → ℝ) (hf : Continuous f)
    (hfi : ∀ i, Integrable f (μ i)) (hfn : Integrable f ν)
    (htail : ∀ ε > 0, ∃ K : Set (Euclidean n), IsCompact K ∧
      (∀ i, (∫ x in Kᶜ, ‖f x‖ ∂μ i) < ε) ∧
      (∫ x in Kᶜ, ‖f x‖ ∂ν) < ε) :
    Tendsto (fun i => ∫ x, f x ∂μ i) atTop (𝓝 (∫ x, f x ∂ν)) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK, hKi, hKn⟩ := htail (ε / 3) (by positivity)
  obtain ⟨χ, hone, _, hcompact, hχ⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let g : C_c(Euclidean n, ℝ) :=
    ⟨⟨fun x => χ x * f x, χ.continuous.mul hf⟩, hcompact.mul_right⟩
  have hgi (i : ℕ) : Integrable (fun x => χ x * f x) (μ i) := by
    letI := hμ i
    exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hgn : Integrable (fun x => χ x * f x) ν := by
    letI := hν
    exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hlim g) (ε / 3) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  have h₁ := (norm_integral_sub_cutoff_le (μ i) f χ K (hfi i) (hgi i)
    (fun x hx => hone hx) hχ).trans_lt (hKi i)
  have h₃ := (norm_integral_sub_cutoff_le ν f χ K hfn hgn
    (fun x hx => hone hx) hχ).trans_lt hKn
  have h₂ := hN i hi
  simp only [Real.dist_eq] at h₂ ⊢
  change |(∫ x, χ x * f x ∂μ i) - ∫ x, χ x * f x ∂ν| < ε / 3 at h₂
  rw [Real.norm_eq_abs] at h₁ h₃
  have ht₁ := abs_sub_le (∫ x, f x ∂μ i) (∫ x, χ x * f x ∂μ i) (∫ x, f x ∂ν)
  have ht₂ := abs_sub_le (∫ x, χ x * f x ∂μ i) (∫ x, χ x * f x ∂ν) (∫ x, f x ∂ν)
  rw [abs_sub_comm (∫ x, χ x * f x ∂ν) (∫ x, f x ∂ν)] at ht₂
  linarith

end Preiss

