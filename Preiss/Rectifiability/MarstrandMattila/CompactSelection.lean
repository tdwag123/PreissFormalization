import Preiss.Rectifiability.WeakApproximation.CompactGeometry
import Preiss.Rectifiability.MarstrandMattila.HausdorffInputs

/-! # Nested compact approximation for finite Hausdorff carriers -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_nested_compact_twoSided_approximation
    (E : Set (Euclidean n)) (hE : MeasurableSet E)
    (hpos : 0 < (Measure.hausdorffMeasure (m : ℝ)) E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞)
    (hu : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), UpperPowerBoundAt m (((Measure.hausdorffMeasure (m : ℝ))).restrict E) x)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    ∃ (F : Set (Euclidean n)) (δ R₀ : ℝ), IsCompact F ∧ F ⊆ E ∧
      0 < (Measure.hausdorffMeasure (m : ℝ)) F ∧ 0 < δ ∧ 0 < R₀ ∧
      (∀ a ∈ F, ∀ r : ℝ, 0 < r → r < R₀ →
        ENNReal.ofReal (δ * r ^ m) ≤ ((Measure.hausdorffMeasure (m : ℝ))).restrict E (ball a r)) ∧
      ∀ η : ℝ, 0 < η → η < 1 → ∃ (G : Set (Euclidean n)) (γ R : ℝ),
        IsCompact G ∧ G ⊆ F ∧ 0 < (Measure.hausdorffMeasure (m : ℝ)) G ∧ 0 < γ ∧ 0 < R ∧ R < R₀ ∧
        TwoSidedApproximation m (((Measure.hausdorffMeasure (m : ℝ))).restrict E) F G η γ R := by
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (m : ℝ)
  let μ := H.restrict E
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfin.ne
  let q : ℕ → ℝ := fun N ↦ 1 / (N + 1 : ℝ)
  have hq (N : ℕ) : 0 < q N := by dsimp [q]; positivity
  have hqmono {i j : ℕ} (hij : i ≤ j) : q j ≤ q i :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  let S : ℕ → Set (Euclidean n) := fun N ↦ weakApproximationGoodSet m μ 1 (q N) (q N)
  have hSm (N : ℕ) : MeasurableSet (S N) :=
    (isClosed_weakApproximationGoodSet μ zero_lt_one (hq N) (hq N)).measurableSet
  have hSmono : Monotone S := fun _ _ hij ↦ weakApproximationGoodSet_mono μ (hqmono hij) (hqmono hij)
  have hcover : ∀ᵐ x ∂μ.restrict E, x ∈ ⋃ N, S N := by
    have hh : ∀ᵐ x ∂μ, MeasureWeaklyLinearlyApproximableAt m μ x := hw
    filter_upwards [ae_restrict_of_ae hh] with x hx
    obtain ⟨N, hN⟩ := (weaklyLinearlyApproximableAt_iff_goodSet_exhaustion μ x).mp hx 1 zero_lt_one
    exact mem_iUnion.mpr ⟨N, hN⟩
  have hposE : 0 < μ E := by simpa only [μ, H, Measure.restrict_apply_self] using hpos
  obtain ⟨N, F, hF, hFsub, hFposμ⟩ :=
    exists_pos_compact_subset_of_ae_mem_iUnion μ E hE hposE S hSm hSmono hcover
  have hFE : F ⊆ E := fun x hx ↦ (hFsub hx).1
  have hFμeq : μ F = H F := by
    dsimp only [μ]
    rw [Measure.restrict_apply hF.measurableSet, inter_eq_left.mpr hFE]
  have hFpos : 0 < H F := by simpa only [hFμeq] using hFposμ
  let δ := q N / 2 ^ m
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlow : ∀ a ∈ F, ∀ r : ℝ, 0 < r → r < q N →
      ENNReal.ofReal (δ * r ^ m) ≤ μ (ball a r) := by
    intro a ha r hr hrR
    obtain ⟨V, _, hlower⟩ := (hFsub ha).2 (r / 2) (half_pos hr) ((half_lt_self hr).trans hrR)
    have hb : ENNReal.ofReal (q N * (r / 2) ^ m) ≤ μ (closedBall a (r / 2)) := by
      simpa only [one_mul] using hlower a (by simp) (mem_ball_self (half_pos hr))
    have heq : δ * r ^ m = q N * (r / 2) ^ m := by dsimp [δ]; rw [div_pow]; ring
    rw [heq]
    exact hb.trans (measure_mono (closedBall_subset_ball (half_lt_self hr)))
  have hrestrict : μ.restrict F = H.restrict F := Measure.restrict_restrict_of_subset hFE
  have hwF : ∀ᵐ x ∂μ.restrict F, MeasureWeaklyLinearlyApproximableAt m (μ.restrict F) x := by
    rw [hrestrict]
    simpa only [WeaklyLinearlyApproximableAt, H] using ae_weaklyLinearlyApproximableAt_subset hE hF.measurableSet hFE hfin hw
  let ν := μ.restrict Fᶜ
  have hνouter : ν.toOuterMeasure = OuterMeasure.restrict (E \ F)
      (OuterMeasure.mkMetric (fun r : ℝ≥0∞ ↦ r ^ (m : ℝ))) := by
    dsimp only [ν, μ]
    rw [Measure.restrict_restrict hF.measurableSet.compl]
    have hset : Fᶜ ∩ E = E \ F := by rw [Set.sdiff_eq, inter_comm]
    rw [hset, Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict (hE.diff hF.measurableSet)]
    simp only [H, Measure.hausdorffMeasure, Measure.mkMetric_toOuterMeasure]
  have hEFcar : MeasurableSet[(Hs_outer (X := Euclidean n) (m : ℝ)).caratheodory] (E \ F) :=
    (OuterMeasure.mkMetric'_isMetric _).le_caratheodory _ (hE.diff hF.measurableSet)
  have hEFfin : (Hs_outer (X := Euclidean n) (m : ℝ)) (E \ F) < ∞ := by
    rw [← hausdorff_measure_eq_outer (m : ℝ) (E \ F)]
    exact (measure_mono sdiff_subset).trans_lt hfin
  have hnull := hausdorffMeasure_upperDensity_eq_zero_ae_notMem (s := (m : ℝ))
    (by positivity) hEFcar hEFfin
  have hO : ∀ᵐ x ∂H, ¬(x ∉ E \ F ∧ dimensional_upper_density ν.toOuterMeasure (m : ℝ) x ≠ 0) := by
    rw [hνouter]
    exact ae_iff.mpr (by simpa only [not_not] using hnull)
  have hsmall : ∀ᵐ x ∂μ.restrict F, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, 0 < r → r < R → (μ.restrict Fᶜ) (ball x r) ≤ ENNReal.ofReal (ε * r ^ m) := by
    rw [hrestrict]
    apply (ae_restrict_iff' hF.measurableSet).mpr
    filter_upwards [hO] with x hx hxF ε hε
    have hzero : dimensional_upper_density ν.toOuterMeasure (m : ℝ) x = 0 := by
      by_contra hne
      exact hx ⟨fun hxEF ↦ hxEF.2 hxF, hne⟩
    have hb : 0 < ε / 2 ^ m := by positivity
    have hlt : dimensional_upper_density ν.toOuterMeasure (m : ℝ) x <
        ENNReal.ofReal (ε / 2 ^ m) := by rw [hzero]; exact ENNReal.ofReal_pos.mpr hb
    obtain ⟨R, hR, hbound⟩ := exists_closedBall_power_bound_of_upperDensity_lt m ν.toOuterMeasure x hb hlt
    refine ⟨R, hR, ?_⟩
    intro r hr hrR
    have hh := hbound r hr hrR
    rw [div_mul_cancel₀ _ (show (2 : ℝ) ^ m ≠ 0 by positivity)] at hh
    exact (measure_mono ball_subset_closedBall).trans hh
  refine ⟨F, δ, q N, hF, hFE, hFpos, hδ, hq N, hlow, ?_⟩
  intro η hη hη1
  obtain ⟨G, γ, R, hG, hGF, hGposμ, hγ, hR, hRR, happ⟩ :=
    exists_compact_twoSided_approximation_of_uniform_lower_bound μ F hF hFposμ hδ (hq N) hlow hwF hsmall hη hη1
  have hGE := hGF.trans hFE
  have hGμeq : μ G = H G := by
    dsimp only [μ]
    rw [Measure.restrict_apply hG.measurableSet, inter_eq_left.mpr hGE]
  refine ⟨G, γ, R, hG, hGF, ?_, hγ, hR, hRR, happ⟩
  simpa only [hGμeq] using hGposμ


end Preiss
