module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Preiss.Rectifiability.Basic
public import Preiss.Geometry.Projections
public import Preiss.Geometry.PlaneMeasure
public import Preiss.Rectifiability.GraphDefs

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def graphMap (V : Plane m n) (f : V.1 → ↥(V.1ᗮ)) (v : V.1) : Euclidean n :=
  (v : Euclidean n) + (f v : Euclidean n)

theorem graphMap_lipschitz_antilipschitz (V : Plane m n)
    (f : V.1 → ↥(V.1ᗮ)) {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (1 + K) (graphMap V f) ∧
      AntilipschitzWith 1 (graphMap V f) ∧
      ∀ v, proj V (graphMap V f v) = (v : Euclidean n) := by
  have hv : LipschitzWith 1 (fun v : V.1 ↦ (v : Euclidean n)) :=
    isometry_subtype_coe.lipschitzWith
  have hfval : LipschitzWith K (fun v : V.1 ↦ (f v : Euclidean n)) := by
    simpa only [one_mul, Function.comp_def] using
      (isometry_subtype_coe.lipschitzWith.comp hf :
        LipschitzWith (1 * K) (fun v : V.1 ↦ (f v : Euclidean n)))
  have hleft (v : V.1) : V.1.orthogonalProjectionOnto (graphMap V f v) = v := by
    rw [graphMap, map_add, V.1.orthogonalProjectionOnto_mem_subspace_eq_self,
      V.1.orthogonalProjectionOnto_apply_of_mem_orthogonal (f v).property, add_zero]
  refine ⟨hv.add hfval, AntilipschitzWith.of_le_mul_dist ?_, ?_⟩
  · intro u v
    simpa only [hleft, NNReal.coe_one, one_mul] using
      V.1.lipschitzWith_orthogonalProjectionOnto.dist_le_mul
        (graphMap V f u) (graphMap V f v)
  · intro v
    exact congrArg (fun w : V.1 ↦ (w : Euclidean n)) (hleft v)

theorem isClosed_and_measure_closedBall_lt_top {s : Set (Euclidean n)}
    (hs : IsLipschitzGraph m s) :
    IsClosed s ∧ ∀ x r, (Measure.hausdorffMeasure (m : ℝ)) (s ∩ closedBall x r) < ∞ := by
  obtain ⟨V, f, ⟨K, hf⟩, rfl⟩ := hs
  have hg := graphMap_lipschitz_antilipschitz V f hf
  refine ⟨hg.2.1.isClosed_range hg.1.uniformContinuous, ?_⟩
  intro x r
  have hb : (Measure.hausdorffMeasure (m : ℝ) : Measure V.1)
      (closedBall (V.1.orthogonalProjectionOnto x) r) < ∞ := by
    have hb' : (Measure.hausdorffMeasure (Module.finrank ℝ V.1 : ℝ) : Measure V.1)
        (closedBall (V.1.orthogonalProjectionOnto x) r) < ∞ :=
      (isCompact_closedBall (V.1.orthogonalProjectionOnto x) r).measure_lt_top
    simpa only [V.property] using hb'
  have hsub : Set.range (graphMap V f) ∩ closedBall x r ⊆
      graphMap V f '' closedBall (V.1.orthogonalProjectionOnto x) r := by
    rintro z ⟨⟨v, rfl⟩, hv⟩
    refine ⟨v, ?_, rfl⟩
    have hleft : V.1.orthogonalProjectionOnto (graphMap V f v) = v :=
      Subtype.ext (hg.2.2 v)
    have hdist := V.1.lipschitzWith_orthogonalProjectionOnto.dist_le_mul
      (graphMap V f v) x
    simp only [hleft, NNReal.coe_one, one_mul] at hdist
    exact hdist.trans hv
  apply lt_of_le_of_lt (measure_mono hsub)
  apply lt_of_le_of_lt (hg.1.hausdorffMeasure_image_le (Nat.cast_nonneg m) _)
  rw [ENNReal.rpow_natCast]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hb

theorem countablyRectifiable_subset_graph {s t : Set (Euclidean n)}
    (hs : IsLipschitzGraph m s) (ht : t ⊆ s) : CountablyRectifiable m t := by
  classical
  obtain ⟨V, f, ⟨K, hf⟩, rfl⟩ := hs
  change t ⊆ Set.range (graphMap V f) at ht
  let e : Euclidean m ≃L[ℝ] V.1 := ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_euclideanSpace_fin, V.property])
  let p : LipschitzPiece m (Euclidean n) :=
    { domain := Set.univ
      toFun := fun u ↦ graphMap V f (e u.val)
      lipschitz := ⟨_, ((graphMap_lipschitz_antilipschitz V f hf).1.comp
        e.lipschitzWith).comp isometry_subtype_coe.lipschitzWith⟩ }
  refine ⟨Set.range (graphMap V f), ⟨{p}, Set.countable_singleton p, ?_⟩, ?_⟩
  · rintro x ⟨v, rfl⟩
    refine mem_iUnion₂.mpr ⟨p, Set.mem_singleton p, ?_⟩
    refine ⟨⟨e.symm v, Set.mem_univ _⟩, ?_⟩
    simp [p]
  · rw [sdiff_eq_empty.mpr ht, measure_empty]

end Preiss
