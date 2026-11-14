module

public import Preiss.Rectifiability.WeakApproximation.Basic
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def negligibleDeletionAt (m : ℕ) (μ : Measure (Euclidean n))
    (s : Set (Euclidean n)) (x : Euclidean n) : Prop :=
  Tendsto (fun r : ℝ ↦ μ (ball x (2 * r) \ s) / ENNReal.ofReal (r ^ m))
    (𝓝[>] 0) (𝓝 0)

theorem weakApproximation_restrict_of_negligible_sdiff
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (F : Set (Euclidean n)) (hF : MeasurableSet F) (x : Euclidean n)
    (h : MeasureWeaklyLinearlyApproximableAt m μ x)
    (herr : negligibleDeletionAt m μ F x) :
    MeasureWeaklyLinearlyApproximableAt m (μ.restrict F) x := by
  intro η hη
  let ε : ℝ := min η 1 / 2
  have hε : 0 < ε := half_pos (lt_min hη zero_lt_one)
  have hεmin : ε ≤ min η 1 := half_le_self (le_min hη.le zero_le_one)
  have hεη : ε ≤ η := hεmin.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεmin.trans (min_le_right _ _)
  obtain ⟨a, ha, R₀, hR₀, happ⟩ := h ε hε
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (ball x (2 * r) \ F) / ENNReal.ofReal (r ^ m) < ENNReal.ofReal (a / 2) :=
    (tendsto_order.mp herr).2 _ (ENNReal.ofReal_pos.mpr (half_pos ha))
  obtain ⟨R₁, hR₁, herror⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨a / 2, half_pos ha, min R₀ R₁, lt_min hR₀ hR₁, ?_⟩
  intro r hr hrR
  obtain ⟨V, hupper, hlower⟩ := happ r hr (hrR.trans_le (min_le_left _ _))
  have hdel : μ (ball x (2 * r) \ F) < ENNReal.ofReal ((a / 2) * r ^ m) := by
    have he := herror ⟨hr, hrR.trans_le (min_le_right _ _)⟩
    have hd : ENNReal.ofReal (r ^ m) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'
    have he' := (ENNReal.div_lt_iff (Or.inl hd) (Or.inl ENNReal.ofReal_ne_top)).mp he
    rwa [← ENNReal.ofReal_mul (half_pos ha).le] at he'
  refine ⟨V, ?_, ?_⟩
  · apply lt_of_le_of_lt (Measure.le_iff'.mp Measure.restrict_le_self _)
    have hsub : ball x r \ {z | infDist (z - x) (V.1 : Set (Euclidean n)) ≤ η * r} ⊆
        ball x r \ {z | infDist (z - x) (V.1 : Set (Euclidean n)) ≤ ε * r} := by
      rintro z ⟨hz, hzt⟩
      refine ⟨hz, ?_⟩
      intro hsmall
      exact hzt (hsmall.trans (mul_le_mul_of_nonneg_right hεη hr.le))
    exact (lt_of_le_of_lt (measure_mono hsub) hupper).trans_le
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hεη (pow_nonneg hr.le m)))
  · intro z hz hzx
    by_contra hnot
    have hsmall : μ.restrict F (ball z (η * r)) < ENNReal.ofReal ((a / 2) * r ^ m) :=
      lt_of_not_ge hnot
    have hsub : ball z (ε * r) ⊆ (ball z (η * r) ∩ F) ∪ (ball x (2 * r) \ F) := by
      intro w hw
      by_cases hwF : w ∈ F
      · exact Or.inl ⟨hw.trans_le (mul_le_mul_of_nonneg_right hεη hr.le), hwF⟩
      · refine Or.inr ⟨?_, hwF⟩
        have hwz : dist w z < ε * r := hw
        have hzx' : dist z x < r := hzx
        have hεr : ε * r ≤ r := mul_le_of_le_one_left hr.le hε1
        have ht := dist_triangle w z x
        change dist w x < 2 * r
        linarith
    have hbound : μ (ball z (ε * r)) ≤
        μ.restrict F (ball z (η * r)) + μ (ball x (2 * r) \ F) := by
      rw [Measure.restrict_apply' hF]
      exact (measure_mono hsub).trans (measure_union_le _ _)
    have hsum := ENNReal.add_lt_add hsmall hdel
    have heq : ENNReal.ofReal ((a / 2) * r ^ m) + ENNReal.ofReal ((a / 2) * r ^ m) =
        ENNReal.ofReal (a * r ^ m) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [heq] at hsum
    exact (not_lt_of_ge (hlower z hz hzx)) (hbound.trans_lt hsum)

end Preiss
