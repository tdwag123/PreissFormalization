module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Algebra.Order.Floor.Ring

/-! # Integrability and integral bounds from countable annular covers

The finite ball mass and summability hypotheses are explicit. The integral cover
bound uses disjointification and applies to any measurable space.
-/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss

theorem integrable_of_summable_annulus_bounds {E F : Type*}
    [NormedAddCommGroup E] [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] (μ : Measure E)
    (hfinite : ∀ R > 0, μ (closedBall 0 R) < ∞)
    (f : E → F) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hbound : ∀ (j : ℕ) (x : E), (j : ℝ) ≤ ‖x‖ →
      ‖x‖ ≤ (j : ℝ) + 1 → ‖f x‖ ≤ M j)
    (hsum : Summable (fun j : ℕ => M j * μ.real (closedBall 0 ((j : ℝ) + 1)))) :
    Integrable f μ := by
  let S : ℕ → Set (E) := fun j => {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ (j : ℝ) + 1}
  have hsub (j : ℕ) : S j ⊆ closedBall 0 ((j : ℝ) + 1) := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hx.2
  have hclosed (j : ℕ) : IsClosed (S j) :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hcompact (j : ℕ) : IsCompact (S j) :=
    (isCompact_closedBall (0 : E) ((j : ℝ) + 1)).of_isClosed_subset
      (hclosed j) (hsub j)
  have hfiniteS (j : ℕ) : μ (S j) < ∞ :=
    (measure_mono (hsub j)).trans_lt (hfinite _ (by positivity))
  have hi (j : ℕ) : IntegrableOn f (S j) μ :=
    hf.continuousOn.integrableOn_of_subset_isCompact (hcompact j)
      (hclosed j).measurableSet Subset.rfl (hfiniteS j).ne
  have hcover : (⋃ j : ℕ, S j) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨⌊‖x‖⌋₊, Nat.floor_le (norm_nonneg x), (Nat.lt_floor_add_one ‖x‖).le⟩
  have hb (j : ℕ) : (∫ x in S j, ‖f x‖ ∂μ) ≤
      M j * μ.real (closedBall 0 ((j : ℝ) + 1)) := by
    have hlocal : (∫ x in S j, ‖f x‖ ∂μ) ≤ M j * μ.real (S j) := by
      have := norm_setIntegral_le_of_norm_le_const (hfiniteS j)
        (fun x hx => (norm_norm (f x)).symm ▸ hbound j x hx.1 hx.2)
      simpa only [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (f x))]
        using this
    exact hlocal.trans (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (hfinite _ (by positivity)).ne (measure_mono (hsub j))) (hM j))
  have hint := integrableOn_iUnion_of_summable_integral_norm hi
    (hsum.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg (f x)) hb)
  simpa only [hcover, integrableOn_univ] using hint

theorem integral_iUnion_le_tsum_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x)
    (S : ℕ → Set X) (hS : ∀ j, MeasurableSet (S j))
    (B : ℕ → ℝ) (hB : Summable B) (hb : ∀ j, (∫ x in S j, f x ∂μ) ≤ B j) :
    (∫ x in ⋃ j, S j, f x ∂μ) ≤ ∑' j, B j := by
  have hdisjbound (j : ℕ) : (∫ x in disjointed S j, f x ∂μ) ≤ B j := by
    apply le_trans _ (hb j)
    exact setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall hpos)
      (Filter.Eventually.of_forall (disjointed_subset S j))
  have hsum : Summable (fun j => ∫ x in disjointed S j, f x ∂μ) :=
    hB.of_nonneg_of_le (fun j => integral_nonneg hpos) hdisjbound
  rw [← iUnion_disjointed (f := S),
    integral_iUnion (fun j => MeasurableSet.disjointed hS j) (disjoint_disjointed S) hf.integrableOn]
  exact hsum.tsum_le_tsum hdisjbound hB

end Preiss
