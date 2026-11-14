module

public import Preiss.Rectifiability.PurelyUnrectifiable
public import Preiss.Rectifiability.Cones
public import Preiss.Rectifiability.ProjectionEstimate
public import Preiss.Rectifiability.WeakApproximation.Uniformization
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem ae_exists_outside_cone_of_purelyUnrectifiable
    (C : Set (Euclidean n)) (hp : PurelyUnrectifiable m C)
    (V : Plane m n) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᵐ a ∂((Measure.hausdorffMeasure (m : ℝ)).restrict C), ∀ r : ℝ, 0 < r →
      ∃ b ∈ C ∩ ball a r, b ∉ cone a V A := by
  classical
  let B (r : ℝ) : Set (Euclidean n) := {a | ∀ b ∈ C,
    r ≤ dist b a ∨ ‖(b - a) - proj V (b - a)‖ ≤ A * ‖proj V (b - a)‖}
  have hproj : Continuous (proj V) :=
    V.1.subtypeL.continuous.comp V.1.orthogonalProjectionOnto.continuous
  have hBclosed (r : ℝ) : IsClosed (B r) := by
    have hBeq : B r = ⋂ b ∈ C, {a : Euclidean n | r ≤ dist b a} ∪
        {a : Euclidean n | ‖(b - a) - proj V (b - a)‖ ≤ A * ‖proj V (b - a)‖} := by
      ext a
      simp only [B, Set.mem_ofPred_eq, mem_iInter, mem_union]
    rw [hBeq]
    apply isClosed_biInter
    intro b _
    have hpcont := hproj.comp (continuous_const.sub continuous_id :
      Continuous (fun a : Euclidean n ↦ b - a))
    exact (isClosed_le continuous_const (continuous_const.dist continuous_id)).union
      (isClosed_le ((continuous_const.sub continuous_id).sub hpcont).norm
        (continuous_const.mul hpcont.norm))
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Euclidean n)
  have : Countable D := hDc.to_subtype
  have hBnull (r : ℝ) (hr : 0 < r) :
      (Measure.hausdorffMeasure (m : ℝ)).restrict C (B r) = 0 := by
    let Z (q : D) := C ∩ B r ∩ ball q.val (r / 4)
    have hZ (q : D) : (Measure.hausdorffMeasure (m : ℝ)) (Z q) = 0 := by
      have hpair : ∀ x ∈ Z q, ∀ y ∈ Z q, y ∈ cone x V A := by
        intro x hx y hy
        have hxq : dist x q.val < r / 4 := hx.2
        have hyq : dist y q.val < r / 4 := hy.2
        have hyx : dist y x < r := by
          have ht := dist_triangle y q.val x
          rw [dist_comm q.val x] at ht
          linarith
        exact (hx.1.2 y hy.1.1).resolve_left (not_le.mpr hyx)
      obtain ⟨f, hf, hsub⟩ := exists_lipschitzGraph_of_pairwise_mem_cone V (Z q) hA hpair
      have hgraph : IsLipschitzGraph m (Set.range (graphMap V f)) := ⟨V, f, hf, rfl⟩
      have hrect := countablyRectifiable_subset_graph hgraph hsub
      have hsubC : Z q ⊆ C ∩ Z q := fun _ hz ↦ ⟨hz.1.1, hz⟩
      exact measure_mono_null hsubC (hp (Z q) hrect)
    rw [Measure.restrict_apply (hBclosed r).measurableSet]
    apply measure_mono_null (t := ⋃ q : D, Z q) ?_ (measure_iUnion_null hZ)
    rintro x ⟨hxB, hxC⟩
    obtain ⟨q, hq, hxq⟩ := hDd.exists_dist_lt x (show 0 < r / 4 by positivity)
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, ⟨hxC, hxB⟩, hxq⟩
  have hall : ∀ᵐ a ∂((Measure.hausdorffMeasure (m : ℝ)).restrict C),
      ∀ j : ℕ, a ∉ B (1 / (j + 1 : ℝ)) := by
    apply ae_all_iff.mpr
    intro j
    exact measure_eq_zero_iff_ae_notMem.mp (hBnull _ (by positivity))
  filter_upwards [hall] with a ha
  intro r hr
  by_contra hno
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hr
  apply ha j
  intro b hb
  by_cases hbr : dist b a < 1 / (j + 1 : ℝ)
  · right
    have hc : b ∈ cone a V A := by
      by_contra hnc
      exact hno ⟨b, ⟨hb, hbr.trans hj⟩, hnc⟩
    exact hc
  · exact Or.inl (le_of_not_gt hbr)

theorem measure_projection_eq_zero_of_purelyUnrectifiable_weakApproximation
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) (hp : PurelyUnrectifiable m E)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' E) = 0 := by sorry

end Preiss
