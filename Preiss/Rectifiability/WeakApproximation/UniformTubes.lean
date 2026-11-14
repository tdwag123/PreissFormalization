module

public import Preiss.Rectifiability.WeakApproximation.Uniformization
public import Mathlib.Tactic

/-! # Compact exhaustion with uniform tube containment and fixed lower mass -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}


set_option maxHeartbeats 1000000 in
theorem exists_compact_uniform_tubes_subset
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ] [μ.Regular]
    (C : Set (Euclidean n)) (hC : MeasurableSet C)
    (hw : ∀ᵐ x ∂μ.restrict C, MeasureWeaklyLinearlyApproximableAt m μ x)
    {δ R₀ η ε : ℝ} (hδ : 0 < δ) (hR₀ : 0 < R₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : 0 < ε)
    (hlower : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r < R₀ →
      ENNReal.ofReal (δ * r ^ m) ≤ μ (ball x r)) :
    ∃ D : Set (Euclidean n), IsCompact D ∧ D ⊆ C ∧ μ (C \ D) < ENNReal.ofReal ε ∧
      ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ a ∈ D, ∀ s : ℝ, 0 < s → s < R₁ →
        ∃ W : Plane m n, D ∩ ball a (2 * s) ⊆ closedTube a W (η * s) := by
  classical
  let α := min (η / 16) (δ * (η / 2) ^ m / (2 * 4 ^ m))
  have hα : 0 < α := by dsimp [α]; positivity
  have hαη : α ≤ η / 16 := min_le_left _ _
  have hαmass : α * 4 ^ m < δ * (η / 2) ^ m := by
    have hh : α ≤ δ * (η / 2) ^ m / (2 * 4 ^ m) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * 4 ^ m)).mp hh
    have hpos : 0 < δ * (η / 2) ^ m := by positivity
    nlinarith
  obtain ⟨D, hD, hDC, hsmall, hgood⟩ := exists_compact_uniform_weakApproximation_subset
    μ C hC hw {α} (by
      intro ζ hζ
      have heq : ζ = α := Finset.mem_singleton.mp hζ
      simpa only [heq] using hα) hε
  obtain ⟨N, hDN⟩ := hgood α (by simp)
  let q : ℝ := 1 / (N + 1 : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨D, hD, hDC, hsmall, min (q / 8) R₀, by positivity, ?_⟩
  intro a ha s hs hsR
  have hs8 : s < q / 8 := hsR.trans_le (min_le_left _ _)
  have hsR₀ : s < R₀ := hsR.trans_le (min_le_right _ _)
  obtain ⟨W, hupper, _⟩ := hDN ha (4 * s) (by positivity) (by change 4 * s < q; linarith)
  have herror : μ (ball a (4 * s) \ closedTube a W (η * s / 2)) <
      ENNReal.ofReal (δ * (η * s / 2) ^ m) := by
    have hsub : ball a (4 * s) \ closedTube a W (η * s / 2) ⊆
        ball a (4 * s) \ closedTube a W (α * (4 * s)) := by
      intro x hx
      refine ⟨hx.1, fun hh ↦ hx.2 ?_⟩
      change infDist (x - a) (W.1 : Set (Euclidean n)) ≤ η * s / 2
      change infDist (x - a) (W.1 : Set (Euclidean n)) ≤ α * (4 * s) at hh
      apply hh.trans
      have hh' := mul_le_mul_of_nonneg_right hαη hs.le
      nlinarith
    apply ((measure_mono hsub).trans hupper).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have heq : (η * s / 2) ^ m = (η / 2) ^ m * s ^ m := by
      rw [← mul_pow]
      congr 1
      ring
    rw [heq, mul_pow]
    have hh := mul_lt_mul_of_pos_right hαmass (pow_pos hs m)
    simpa only [mul_assoc] using hh
  have hhalf : (η / 2) * (2 * s) / 2 = η * s / 2 := by ring
  have hfull : (η / 2) * (2 * s) = η * s := by ring
  have htube := subset_tube_of_lower_mass_and_small_outside_mass μ D a W hδ
    (show 0 < η / 2 by positivity) (show η / 2 ≤ 1 by linarith) (show 0 < 2 * s by positivity)
    (fun z hz ↦ by
      rw [hhalf]
      apply hlower z (hDC hz) (η * s / 2) (by positivity)
      have hh := mul_le_mul_of_nonneg_right hη1 hs.le
      linarith)
    (by rw [hhalf, show 2 * (2 * s) = 4 * s by ring]; exact herror)
  refine ⟨W, ?_⟩
  simpa only [hfull] using htube

end Preiss
