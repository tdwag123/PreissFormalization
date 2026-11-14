import Preiss.Density.HausdorffComparison
import FormalizingGMT.TangentMeasures.DensityIneqToTangentsLemmas2

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_goodSet_mem_of_density_bounds (μ : Measure (Euclidean n))
    (x : Euclidean n) (h : HasPositiveFiniteDensitiesAt m μ x) :
    ∃ (p q : ℚ) (k : ℕ), 0 < (p : ℝ) ∧ 0 < (q : ℝ) ∧
      x ∈ goodSet (m : ℝ) (p : ℝ) (q : ℝ) k μ := by
  have hratio : 0 < RatioOfDensities (m : ℝ) μ x :=
    ENNReal.div_pos h.1.ne' h.2.ne
  obtain ⟨θ, _, hθ, hθratio⟩ := ENNReal.lt_iff_exists_real_btwn.mp hratio
  have hx : x ∈ positiveFiniteDensitySet (m : ℝ) μ :=
    ⟨h.1, lower_le_upper_density (m : ℝ) x, h.2⟩
  obtain ⟨p, q, k, hp, hq, _, _, hxg⟩ :=
    exists_goodSet_mem hx (ENNReal.ofReal_pos.mp hθ) hθratio
  exact ⟨p, q, k, hp, hq, hxg⟩

theorem exists_finite_hausdorff_pieces_of_density_bounds
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x) :
    ∃ S : ℕ → Set (Euclidean n), (∀ j, MeasurableSet (S j)) ∧
      (∀ j, Bornology.IsBounded (S j)) ∧
      (∀ j, (Measure.hausdorffMeasure (m : ℝ)) (S j) < ∞) ∧
      μ (⋃ j, S j)ᶜ = 0 ∧ ∀ j, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        ENNReal.ofReal a • (Measure.hausdorffMeasure (m : ℝ)).restrict (S j) ≤ μ.restrict (S j) ∧
        μ.restrict (S j) ≤ ENNReal.ofReal b • (Measure.hausdorffMeasure (m : ℝ)).restrict (S j) := by
  classical
  let I := {p : ℚ // 0 < (p : ℝ)} × {q : ℚ // 0 < (q : ℝ)} × ℕ × ℕ
  let T : I → Set (Euclidean n) := fun i ↦
    goodSet (m : ℝ) (i.1.val : ℝ) (i.2.1.val : ℝ) i.2.2.1 μ ∩
      closedBall 0 (i.2.2.2 : ℝ)
  have hT (i : I) : MeasurableSet (T i) :=
    ((isClosed_goodSet _ _ _ _ μ).inter isClosed_closedBall).measurableSet
  have hTb (i : I) : Bornology.IsBounded (T i) :=
    isBounded_closedBall.subset inter_subset_right
  obtain ⟨C, hC, hlower⟩ := hausdorff_restrict_le_measure_of_ball_bounds m n
  have hlo (i : I) : (Measure.hausdorffMeasure (m : ℝ)).restrict (T i) ≤
      ENNReal.ofReal (C / ((i.1.val : ℝ) / 2 ^ m)) • μ.restrict (T i) := by
    apply hlower μ (T i) ((i.1.val : ℝ) / 2 ^ m) (1 / (i.2.2.1 + 1 : ℝ))
      (hT i) (div_pos i.1.property (by positivity)) (by positivity)
    intro x hx r hr hrR
    have hhalf : r / 2 < 1 / (i.2.2.1 + 1 : ℝ) := by linarith
    have hb := (hx.1 (r / 2) (by positivity) hhalf).1
    have heq : (i.1.val : ℝ) * (r / 2) ^ (m : ℝ) =
        ((i.1.val : ℝ) / 2 ^ m) * r ^ m := by
      rw [Real.rpow_natCast, div_pow]
      ring
    rw [heq] at hb
    exact hb.trans (measure_mono (closedBall_subset_ball (by linarith : r / 2 < r)))
  have hhi (i : I) : μ.restrict (T i) ≤
      ENNReal.ofReal (i.2.1.val : ℝ) • (Measure.hausdorffMeasure (m : ℝ)).restrict (T i) := by
    apply measure_restrict_le_hausdorff_of_uniform_ball_upper_bound m μ (T i) (hT i)
      (i.2.1.val : ℝ) (1 / (i.2.2.1 + 1 : ℝ)) i.2.1.property (by positivity)
    intro x hx r hr hrR
    exact (measure_mono ball_subset_closedBall).trans
      (by simpa only [Real.rpow_natCast] using (hx.1 r hr hrR).2)
  have hfinite (i : I) : (Measure.hausdorffMeasure (m : ℝ)) (T i) < ∞ := by
    have hi := Measure.le_iff'.mp (hlo i) (T i)
    simp only [Measure.restrict_apply' (hT i), inter_self, Measure.smul_apply, smul_eq_mul] at hi
    have hμfin : μ (T i) < ∞ := (hTb i).measure_lt_top
    exact hi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμfin)
  have hI : (Set.univ : Set I).Nonempty :=
    ⟨(⟨1, by norm_num⟩, ⟨1, by norm_num⟩, 0, 0), mem_univ _⟩
  obtain ⟨e, he⟩ := (Set.to_countable (Set.univ : Set I)).exists_eq_range hI
  have hsurj : Function.Surjective e := by
    intro i
    have hi : i ∈ Set.range e := by rw [← he]; exact mem_univ _
    exact hi
  have hcover : ∀ᵐ x ∂μ, x ∈ ⋃ j, T (e j) := by
    filter_upwards [h] with x hx
    obtain ⟨p, q, k, hp, hq, hxg⟩ := exists_goodSet_mem_of_density_bounds μ x hx
    obtain ⟨l, hl⟩ := exists_nat_gt ‖x‖
    let i : I := (⟨p, hp⟩, ⟨q, hq⟩, k, l)
    obtain ⟨j, hj⟩ := hsurj i
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [hj]
    exact ⟨hxg, by simpa only [mem_closedBall, dist_zero_right] using hl.le⟩
  refine ⟨fun j ↦ T (e j), fun j ↦ hT (e j), fun j ↦ hTb (e j),
    fun j ↦ hfinite (e j), ?_, ?_⟩
  · apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcover] with x hx
    exact fun hxnot ↦ hxnot hx
  · intro j
    let d : ℝ := C / (((e j).1.val : ℝ) / 2 ^ m)
    have hd : 0 < d := div_pos hC (div_pos (e j).1.property (by positivity))
    refine ⟨1 / d, ((e j).2.1.val : ℝ), one_div_pos.mpr hd, (e j).2.1.property, ?_, hhi (e j)⟩
    apply Measure.le_iff'.mpr
    intro A
    rw [Measure.smul_apply, smul_eq_mul]
    have hi := Measure.le_iff'.mp (hlo (e j)) A
    simp only [Measure.smul_apply, smul_eq_mul] at hi
    change (Measure.hausdorffMeasure (m : ℝ)).restrict (T (e j)) A ≤
      ENNReal.ofReal d * μ.restrict (T (e j)) A at hi
    calc
      ENNReal.ofReal (1 / d) * (Measure.hausdorffMeasure (m : ℝ)).restrict (T (e j)) A
          ≤ ENNReal.ofReal (1 / d) * (ENNReal.ofReal d * μ.restrict (T (e j)) A) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = μ.restrict (T (e j)) A := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          one_div_mul_cancel hd.ne', ENNReal.ofReal_one, one_mul]

end Preiss
