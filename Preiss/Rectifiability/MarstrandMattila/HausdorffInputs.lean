import Preiss.Rectifiability.WeakApproximation.Density
import Preiss.Density.Defs
import Preiss.Density.LowerBounds
import Preiss.Density.UpperBounds
import Preiss.Density.PowerComparison
import FormalizingGMT.Densities.HausdorffUpperDensityInside
import FormalizingGMT.Densities.HausdorffUpperDensityOutside

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

/-- The finite-Hausdorff upper-density bound, expressed in the pure power-bound
API consumed by the packing theorem. Ambient Hausdorff measure need not be sigma-finite. -/
theorem ae_upperPowerBoundAt_restrict_hausdorff (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : Measure.hausdorffMeasure (m : ℝ) E < ∞) :
    ∀ᵐ x ∂((Measure.hausdorffMeasure (m : ℝ)).restrict E),
      UpperPowerBoundAt m ((Measure.hausdorffMeasure (m : ℝ)).restrict E) x := by
  have hEcar : MeasurableSet[(OuterMeasure.mkMetric (X := Euclidean n)
      (fun r : ℝ≥0∞ ↦ r ^ (m : ℝ))).caratheodory] E :=
    (OuterMeasure.mkMetric'_isMetric _).le_caratheodory _ hE
  have hnull := hausdorffMeasure_upperDensity_le_one_ae_mem (s := (m : ℝ))
    (by positivity) E hEcar hfin.ne
  apply (ae_restrict_iff' hE).mpr
  have he : ∀ᵐ x ∂(Measure.hausdorffMeasure (m : ℝ)),
      ¬(x ∈ E ∧ 1 < dimensional_upper_density
        ((Measure.hausdorffMeasure (m : ℝ)).restrict E).toOuterMeasure (m : ℝ) x) :=
    ae_iff.mpr (by simpa only [not_not] using hnull)
  filter_upwards [he] with x hx hxE
  have hle : dimensional_upper_density
      ((Measure.hausdorffMeasure (m : ℝ)).restrict E).toOuterMeasure (m : ℝ) x ≤ 1 :=
    le_of_not_gt fun hh ↦ hx ⟨hxE, hh⟩
  obtain ⟨C, R, hC, hR, hball⟩ := exists_closedBall_upper_bound_of_upperDensity_lt_top
    ((Measure.hausdorffMeasure (m : ℝ)).restrict E) x (hle.trans_lt (by simp))
  exact ⟨C, R, hC, hR, fun r hr hrR ↦ (measure_mono ball_subset_closedBall).trans (hball r hr hrR)⟩

theorem lower_density_pos_of_weakApproximation (μ : Measure (Euclidean n)) (x : Euclidean n)
    (h : MeasureWeaklyLinearlyApproximableAt m μ x) :
    0 < dimensional_lower_density μ.toOuterMeasure (m : ℝ) x := by
  obtain ⟨a, R, ha, hR, hball⟩ := lower_power_bound_of_weakApproximation μ x h
  exact (ENNReal.ofReal_pos.mpr (div_pos ha (by positivity))).trans_le
    (lower_density_ge_of_ball_power_lower_bound m μ.toOuterMeasure x ha.le hR hball)

theorem ae_weaklyLinearlyApproximableAt_subset {E F : Set (Euclidean n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hFE : F ⊆ E)
    (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) (h : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict F), WeaklyLinearlyApproximableAt m F x := by
  have hEFcar : MeasurableSet[(Hs_outer (X := Euclidean n) (m : ℝ)).caratheodory] (E \ F) :=
    (OuterMeasure.mkMetric'_isMetric _).le_caratheodory _ (hE.diff hF)
  have hEFfin : (Hs_outer (X := Euclidean n) (m : ℝ)) (E \ F) < ∞ := by
    rw [← hausdorff_measure_eq_outer (m : ℝ) (E \ F)]
    exact (measure_mono sdiff_subset).trans_lt hfin
  have hnull := hausdorffMeasure_upperDensity_eq_zero_ae_notMem (s := (m : ℝ))
    (by positivity) hEFcar hEFfin
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (m : ℝ)
  haveI : IsFiniteMeasure (H.restrict E) := isFiniteMeasure_restrict.mpr hfin.ne
  have houter : (H.restrict (E \ F)).toOuterMeasure =
      OuterMeasure.restrict (E \ F) (OuterMeasure.mkMetric (fun r : ℝ≥0∞ ↦ r ^ (m : ℝ))) := by
    rw [Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict (hE.diff hF)]
    simp only [H, Measure.hausdorffMeasure, Measure.mkMetric_toOuterMeasure]
  have hcompl : (H.restrict E).restrict Fᶜ = H.restrict (E \ F) := by
    rw [Measure.restrict_restrict hF.compl]
    simp only [Set.sdiff_eq, inter_comm]
  have he : ∀ᵐ x ∂H, ¬(x ∉ E \ F ∧ dimensional_upper_density
      (H.restrict (E \ F)).toOuterMeasure (m : ℝ) x ≠ 0) := by
    rw [houter]
    exact ae_iff.mpr (by simpa only [not_not] using hnull)
  apply (ae_restrict_iff' hF).mpr
  have hw := (ae_restrict_iff' hE).mp h
  filter_upwards [hw, he] with x hx hex hxF
  have hzero : dimensional_upper_density (H.restrict (E \ F)).toOuterMeasure (m : ℝ) x = 0 := by
    by_contra hne
    exact hex ⟨fun hxEF ↦ hxEF.2 hxF, hne⟩
  have hdel : negligibleDeletionAt m (H.restrict E) F x := by
    apply negligibleDeletionAt_of_upperDensity_restrict_compl_eq_zero _ F hF x
    simpa only [hcompl] using hzero
  have hres := weakApproximation_restrict_of_negligible_sdiff (H.restrict E) F hF x
    (hx (hFE hxF)) hdel
  simpa only [WeaklyLinearlyApproximableAt, H, Measure.restrict_restrict_of_subset hFE] using hres

theorem exists_upper_mass_small_sdiff_point (m n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E G : Set (Euclidean n)),
      MeasurableSet E → MeasurableSet G → G ⊆ E → (Measure.hausdorffMeasure (m : ℝ)) E < ∞ → 0 < (Measure.hausdorffMeasure (m : ℝ)) G →
      ∀ t : ℝ, 0 < t → ∃ (a : Euclidean n) (R : ℝ), a ∈ G ∧ 0 < R ∧
        ∀ r : ℝ, 0 < r → r < R →
          ((Measure.hausdorffMeasure (m : ℝ))).restrict E (ball a r) ≤ ENNReal.ofReal (C * r ^ m) ∧
          (Measure.hausdorffMeasure (m : ℝ)) ((E \ G) ∩ ball a (2 * r)) ≤ ENNReal.ofReal (t * r ^ m) := by sorry

end Preiss
