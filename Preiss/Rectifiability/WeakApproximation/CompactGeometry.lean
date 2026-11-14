module

public import Preiss.Rectifiability.WeakApproximation.TwoSided
public import Preiss.Rectifiability.WeakApproximation.Uniformization
public import Preiss.Density.UpperBallSets
public import Preiss.Analysis.CompactExhaustion
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Compact sets with common-plane geometric approximation

The plane is selected once, at radius `4 * r`, for the restricted measure.
The deleted mass bound upgrades its tube estimate to the original measure.
-/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_compact_twoSided_approximation_of_uniform_lower_bound
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ] [μ.Regular]
    (F : Set (Euclidean n)) (hF : IsCompact F) (hpos : 0 < μ F)
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀ : 0 < R₀)
    (hlow : ∀ a ∈ F, ∀ r : ℝ, 0 < r → r < R₀ →
      ENNReal.ofReal (δ * r ^ m) ≤ μ (ball a r))
    (hw : ∀ᵐ x ∂μ.restrict F, MeasureWeaklyLinearlyApproximableAt m (μ.restrict F) x)
    (hsmall : ∀ᵐ x ∂μ.restrict F, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, 0 < r → r < R → (μ.restrict Fᶜ) (ball x r) ≤ ENNReal.ofReal (ε * r ^ m))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (G : Set (Euclidean n)) (γ R : ℝ),
      IsCompact G ∧ G ⊆ F ∧ 0 < μ G ∧ 0 < γ ∧ 0 < R ∧ R < R₀ ∧
      TwoSidedApproximation m μ F G η γ R := by
  let μF := μ.restrict F
  let ν := μ.restrict Fᶜ
  let ε := min (η / 16) (δ * (η / 2) ^ m / (4 * 4 ^ m))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεη : ε ≤ η / 16 := min_le_left _ _
  have hεcoef : ε * (4 * 4 ^ m) ≤ δ * (η / 2) ^ m :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hcoef : 2 * ε * 4 ^ m < δ * (η / 2) ^ m := by
    have hp : 0 < δ * (η / 2) ^ m := by positivity
    nlinarith
  let q : ℕ → ℝ := fun N ↦ 1 / (N + 1 : ℝ)
  have hq (N : ℕ) : 0 < q N := by dsimp [q]; positivity
  have hqmono {i j : ℕ} (hij : i ≤ j) : q j ≤ q i :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  let S : ℕ → Set (Euclidean n) := fun N ↦
    weakApproximationGoodSet m μF ε (q N) (q N) ∩ ballPowerUpperBoundSet m ν ε (q N)
  have hSm (N : ℕ) : MeasurableSet (S N) :=
    ((isClosed_weakApproximationGoodSet μF hε (hq N) (hq N)).inter
      (isClosed_ballPowerUpperBoundSet m ν ε (q N))).measurableSet
  have hSmono : Monotone S := by
    intro i j hij x hx
    exact ⟨weakApproximationGoodSet_mono μF (hqmono hij) (hqmono hij) hx.1,
      ballPowerUpperBoundSet_mono m ν le_rfl (hqmono hij) hx.2⟩
  have hcover : ∀ᵐ x ∂μF.restrict F, x ∈ ⋃ N, S N := by
    have hh : ∀ᵐ x ∂μF, x ∈ ⋃ N, S N := by
      filter_upwards [hw, hsmall] with x hxw hxs
      obtain ⟨N, hN⟩ := (weaklyLinearlyApproximableAt_iff_goodSet_exhaustion μF x).mp hxw ε hε
      obtain ⟨R, hR, hbound⟩ := hxs ε hε
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt hR
      refine mem_iUnion.mpr ⟨max N M, ?_⟩
      refine ⟨weakApproximationGoodSet_mono μF (hqmono (le_max_left _ _))
        (hqmono (le_max_left _ _)) hN, ?_⟩
      intro r hr hrM
      exact hbound r hr (hrM.trans ((hqmono (le_max_right _ _)).trans_lt hM))
    exact ae_restrict_of_ae hh
  have hposF : 0 < μF F := by simpa only [μF, Measure.restrict_apply_self] using hpos
  obtain ⟨N, G, hG, hGsub, hGpos⟩ := exists_pos_compact_subset_of_ae_mem_iUnion μF F
    hF.measurableSet hposF S hSm hSmono hcover
  have hGF : G ⊆ F := fun x hx ↦ (hGsub hx).1
  have hGμ : 0 < μ G := hGpos.trans_le (Measure.le_iff'.mp Measure.restrict_le_self G)
  let R := min (q N / 4) (R₀ / 2)
  have hR : 0 < R := lt_min (by positivity) (half_pos hR₀)
  have hRR : R < R₀ := (min_le_right _ _).trans_lt (half_lt_self hR₀)
  refine ⟨G, q N, R, hG, hGF, hGμ, hq N, hR, hRR,
    nonempty_of_measure_ne_zero hpos.ne', ?_⟩
  intro a ha r hr hrR
  have hr₀ : r < R₀ := hrR.trans hRR
  have hr4 : 0 < 4 * r := by positivity
  have hr4q : 4 * r < q N := by have hh := hrR.trans_le (min_le_left _ _); linarith
  have haS := (hGsub ha).2
  obtain ⟨V, hupper, hlower⟩ := haS.1 (4 * r) hr4 hr4q
  have hνupper := haS.2 (4 * r) hr4 hr4q
  have hεr := mul_le_mul_of_nonneg_right hεη hr.le
  have hηr : η * r < r := mul_lt_of_lt_one_left hr hη1
  have hεstrict : ε * (4 * r) < η * r := by nlinarith
  have hεhalf : ε * (4 * r) ≤ η * r / 2 := by nlinarith
  have herror : μ (ball a (4 * r) \ closedTube a V (η * r / 2)) <
      ENNReal.ofReal (δ * (η * r / 2) ^ m) := by
    let A := ball a (4 * r) \ closedTube a V (ε * (4 * r))
    have hsub : ball a (4 * r) \ closedTube a V (η * r / 2) ⊆ A := by
      rintro z ⟨hz, hzt⟩
      exact ⟨hz, fun hh ↦ hzt (hh.trans hεhalf)⟩
    have hsplit : μ A = μF A + ν A := by
      have hh := congrArg (fun ρ : Measure (Euclidean n) ↦ ρ A)
        (Measure.restrict_add_restrict_compl (μ := μ) hF.measurableSet)
      simpa only [Measure.add_apply, μF, ν] using hh.symm
    calc
      μ (ball a (4 * r) \ closedTube a V (η * r / 2)) ≤ μ A := measure_mono hsub
      _ = μF A + ν A := hsplit
      _ ≤ ENNReal.ofReal (ε * (4 * r) ^ m) + ENNReal.ofReal (ε * (4 * r) ^ m) :=
        add_le_add hupper ((measure_mono sdiff_subset).trans hνupper)
      _ = ENNReal.ofReal (2 * (ε * (4 * r) ^ m)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ < ENNReal.ofReal (δ * (η * r / 2) ^ m) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        have hh := mul_lt_mul_of_pos_right hcoef (pow_pos hr m)
        rw [show η * r / 2 = (η / 2) * r by ring, mul_pow, mul_pow]
        nlinarith
  have hfour : 2 * (2 * r) = 4 * r := by ring
  have hhalf : (η / 2) * (2 * r) / 2 = η * r / 2 := by ring
  have hfull : (η / 2) * (2 * r) = η * r := by ring
  have hlow' : ∀ z ∈ F, ENNReal.ofReal (δ * ((η / 2) * (2 * r) / 2) ^ m) ≤
      μ (ball z ((η / 2) * (2 * r) / 2)) := by
    intro z hz
    rw [hhalf]
    apply hlow z hz _ (by positivity)
    have hh : η * r < r := mul_lt_of_lt_one_left hr hη1
    linarith
  have htube := subset_tube_of_lower_mass_and_small_outside_mass μ F a V hδ (half_pos hη)
    (by linarith : η / 2 ≤ 1) (show 0 < 2 * r by positivity) hlow'
    (by simpa only [hfour, hhalf] using herror)
  refine ⟨V, by simpa only [hfull] using htube, ?_, ?_⟩
  · intro z hz hzr
    have hzr4 : z ∈ ball a (4 * r) := ball_subset_ball (by linarith) hzr
    have hmass : 0 < μF (closedBall z (ε * (4 * r))) :=
      (ENNReal.ofReal_pos.mpr (mul_pos (hq N) (pow_pos hr4 m))).trans_le (hlower z hz hzr4)
    have hmass' : μ (closedBall z (ε * (4 * r)) ∩ F) ≠ 0 := by
      rw [← Measure.restrict_apply isClosed_closedBall.measurableSet]
      exact hmass.ne'
    obtain ⟨w, hwball, hwF⟩ := nonempty_of_measure_ne_zero hmass'
    exact (infDist_le_dist_of_mem hwF).trans_lt
      ((show dist z w ≤ ε * (4 * r) by simpa only [mem_closedBall, dist_comm] using hwball).trans_lt hεstrict)
  · intro z hz hzr
    have hzr4 : z ∈ ball a (4 * r) := ball_subset_ball (by linarith) hzr
    calc
      ENNReal.ofReal (q N * (η * r) ^ m) ≤ ENNReal.ofReal (q N * (4 * r) ^ m) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (hq N).le
        exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ η * r) (by nlinarith : η * r ≤ 4 * r) m
      _ ≤ μF (closedBall z (ε * (4 * r))) := hlower z hz hzr4
      _ ≤ μ (closedBall z (ε * (4 * r))) := Measure.le_iff'.mp Measure.restrict_le_self _
      _ ≤ μ (ball z (η * r)) := measure_mono (closedBall_subset_ball hεstrict)

end Preiss
