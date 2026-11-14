module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! # Hausdorff comparison from uniform lower ball bounds

The covering estimate works in any separable metric Borel space.
Only the final comparison against the original set requires outer regularity.
-/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace Preiss
variable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_small_cover_of_ball_lower_bound (m : ℕ) (μ : Measure X)
    (A U : Set X) (hU : IsOpen U) (hAU : A ⊆ U)
    (a R ε : ℝ) (ha : 0 < a) (hR : 0 < R) (hε : 0 < ε)
    (hbound : ∀ x ∈ A, ∀ r : ℝ, 0 < r → r < R →
      ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r)) :
    ∃ u : Set (X × ℝ), u.Countable ∧
      (∀ b ∈ u, ediam (ball b.1 (5 * b.2)) ≤ ENNReal.ofReal ε) ∧
      A ⊆ ⋃ b ∈ u, ball b.1 (5 * b.2) ∧
      (∑' b : u, ediam (ball b.1.1 (5 * b.1.2)) ^ (m : ℝ)) ≤
        ENNReal.ofReal (10 ^ m / a) * μ U := by
  classical
  let T : Set (X × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧ b.2 < R ∧
    b.2 < ε / 10 ∧ ball b.1 b.2 ⊆ U}
  obtain ⟨u, huT, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball T Prod.fst Prod.snd
      (ε / 10) (fun b hb => hb.2.2.2.1.le) 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun b hb => ⟨b.1, mem_ball_self (huT hb).2.1⟩)
  letI : Countable u := huc.to_subtype
  have hd (b : X × ℝ) (hb : b ∈ u) :
      ediam (ball b.1 (5 * b.2)) ≤ ENNReal.ofReal (10 * b.2) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' := mem_ball.mp hx
    have hy' := mem_ball.mp hy
    calc
      dist x y ≤ dist x b.1 + dist y b.1 := dist_triangle_right _ _ _
      _ ≤ 10 * b.2 := by linarith
  refine ⟨u, huc, ?_, ?_, ?_⟩
  · intro b hb
    exact (hd b hb).trans (ENNReal.ofReal_le_ofReal (by linarith [(huT hb).2.2.2.1]))
  · intro x hx
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU x (hAU hx)
    let r := min (min R δ) (ε / 10) / 2
    have hmin : 0 < min (min R δ) (ε / 10) := by positivity
    have hr : 0 < r := by dsimp [r]; positivity
    have hrR : r < R := by
      have := min_le_left (min R δ) (ε / 10)
      have := min_le_left R δ
      dsimp [r]
      linarith
    have hrε : r < ε / 10 := by
      have := min_le_right (min R δ) (ε / 10)
      dsimp [r]
      linarith
    have hrδ : r ≤ δ := by
      have := min_le_left (min R δ) (ε / 10)
      have := min_le_right R δ
      dsimp [r]
      linarith
    have hxT : (x, r) ∈ T := ⟨hx, hr, hrR, hrε, (ball_subset_ball hrδ).trans hδU⟩
    obtain ⟨b, hb, hxb⟩ := hcover (x, r) hxT
    exact mem_iUnion₂.mpr ⟨b, hb, hxb (mem_ball_self hr)⟩
  · have hcost (b : u) : ediam (ball b.1.1 (5 * b.1.2)) ^ (m : ℝ) ≤
        ENNReal.ofReal (10 ^ m / a) * μ (ball b.1.1 b.1.2) := by
      have hb := huT b.property
      have hrpos : 0 < b.1.2 := hb.2.1
      calc
        _ ≤ ENNReal.ofReal (10 * b.1.2) ^ (m : ℝ) :=
          ENNReal.rpow_le_rpow (hd b.1 b.property) (Nat.cast_nonneg m)
        _ = ENNReal.ofReal ((10 * b.1.2) ^ m) := by
          rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity)]
        _ = ENNReal.ofReal (10 ^ m / a) * ENNReal.ofReal (a * b.1.2 ^ m) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [mul_pow]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hbound _ hb.1 _ hb.2.1 hb.2.2.1) bot_le
    have hsum : (∑' b : u, μ (ball b.1.1 b.1.2)) =
        μ (⋃ b : u, ball b.1.1 b.1.2) := by
      symm
      apply measure_iUnion
      · intro b c hbc
        exact hdisj b.property c.property (fun heq => hbc (Subtype.ext heq))
      · intro b
        exact measurableSet_ball
    calc
      _ ≤ ∑' b : u, ENNReal.ofReal (10 ^ m / a) * μ (ball b.1.1 b.1.2) :=
        ENNReal.tsum_le_tsum hcost
      _ = ENNReal.ofReal (10 ^ m / a) * μ (⋃ b : u, ball b.1.1 b.1.2) := by
        rw [ENNReal.tsum_mul_left, hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (measure_mono (iUnion_subset fun b => (huT b.property).2.2.2.2)) bot_le

theorem hausdorff_le_open_mass_of_ball_lower_bound (m : ℕ) (μ : Measure X)
    (A U : Set X) (hU : IsOpen U) (hAU : A ⊆ U)
    (a R : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hbound : ∀ x ∈ A, ∀ r : ℝ, 0 < r → r < R →
      ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r)) :
    (Measure.hausdorffMeasure (m : ℝ)) A ≤ ENNReal.ofReal (10 ^ m / a) * μ U := by
  classical
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  choose u huc hd hcover hsum using fun j =>
    exists_small_cover_of_ball_lower_bound m μ A U hU hAU a R (δ j) ha hR (hδ j) hbound
  letI (j : ℕ) : Countable (u j) := (huc j).to_subtype
  have hδlim : Tendsto (fun j => ENNReal.ofReal (δ j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, δ, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto δ atTop (𝓝 0))
  have hH := Measure.hausdorffMeasure_le_liminf_tsum (m : ℝ) A
    (fun j => ENNReal.ofReal (δ j)) hδlim
    (fun j (b : u j) => ball b.1.1 (5 * b.1.2))
    (Filter.Eventually.of_forall fun j b => hd j b.1 b.property)
    (Filter.Eventually.of_forall fun j => by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp (hcover j hx)
      exact mem_iUnion.mpr ⟨⟨b, hb⟩, hxb⟩)
  exact hH.trans (liminf_le_of_frequently_le' (Filter.Eventually.of_forall hsum).frequently)

theorem hausdorff_le_measure_of_uniform_ball_lower_bound (m : ℕ) (μ : Measure X)
    [μ.OuterRegular] (A : Set X) (a R : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hbound : ∀ x ∈ A, ∀ r : ℝ, 0 < r → r < R →
      ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r)) :
    (Measure.hausdorffMeasure (m : ℝ)) A ≤ ENNReal.ofReal (10 ^ m / a) * μ A := by
  have hc : ENNReal.ofReal (10 ^ m / a) ≠ 0 := by positivity
  rw [A.measure_eq_iInf_isOpen μ]
  simp only [ENNReal.mul_iInf_of_ne hc ENNReal.ofReal_ne_top]
  refine le_iInf fun U => le_iInf fun hAU => le_iInf fun hU => ?_
  exact hausdorff_le_open_mass_of_ball_lower_bound m μ A U hU hAU a R ha hR hbound

theorem hausdorff_restrict_le_measure_of_uniform_ball_lower_bound
    (m : ℕ) (μ : Measure X) [μ.OuterRegular] (S : Set X) (hS : MeasurableSet S)
    (a R : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hbound : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r < R →
      ENNReal.ofReal (a * r ^ m) ≤ μ (ball x r)) :
    (Measure.hausdorffMeasure (m : ℝ)).restrict S ≤ ENNReal.ofReal (10 ^ m / a) • μ.restrict S := by
  apply Measure.le_iff'.mpr
  intro t
  simp only [Measure.restrict_apply' hS, Measure.smul_apply, smul_eq_mul]
  exact hausdorff_le_measure_of_uniform_ball_lower_bound m μ (t ∩ S) a R ha hR
    (fun x hx => hbound x hx.2)

end Preiss
