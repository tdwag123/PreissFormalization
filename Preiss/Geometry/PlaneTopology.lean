module

public import Preiss.Geometry.Projections
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def rankProjectionSet (m n : ℕ) : Set (Euclidean n →L[ℝ] Euclidean n) :=
  {P | P.adjoint = P ∧ P.comp P = P ∧ Module.finrank ℝ (LinearMap.range P.toLinearMap) = m}

theorem range_planeProjection :
    Set.range (planeProjection (m := m) (n := n)) = rankProjectionSet m n := by
  ext P
  constructor
  · rintro ⟨V, rfl⟩
    refine ⟨isSelfAdjoint_starProjection V.1, V.1.isIdempotentElem_starProjection, ?_⟩
    change Module.finrank ℝ V.1.starProjection.range = m
    rw [Submodule.range_starProjection]
    exact V.property
  · rintro ⟨hadj, hidem, hrank⟩
    have hp : IsStarProjection P := ⟨hidem, hadj⟩
    obtain ⟨_, hP⟩ := isStarProjection_iff_eq_starProjection_range.mp hp
    exact ⟨⟨P.range, hrank⟩, hP.symm⟩

theorem isCompact_rankProjectionSet (m n : ℕ) : IsCompact (rankProjectionSet m n) := by
  let tr : (Euclidean n →L[ℝ] Euclidean n) →ₗ[ℝ] ℝ :=
    { toFun := fun P ↦ LinearMap.trace ℝ (Euclidean n) P.toLinearMap
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have htrace (P : Euclidean n →L[ℝ] Euclidean n) (hp : IsIdempotentElem P) :
      tr P = (Module.finrank ℝ P.range : ℝ) :=
    (LinearMap.IsIdempotentElem.isProj_range P.toLinearMap
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr hp)).trace
  have hchar : rankProjectionSet m n =
      {P : Euclidean n →L[ℝ] Euclidean n | P.adjoint = P ∧ P * P = P ∧ tr P = (m : ℝ)} := by
    ext P
    constructor
    · rintro ⟨ha, hi, hr⟩
      refine ⟨ha, hi, ?_⟩
      rw [htrace P hi, hr]
    · rintro ⟨ha, hi, ht⟩
      refine ⟨ha, hi, ?_⟩
      exact Nat.cast_injective ((htrace P hi).symm.trans ht)
  have hclosed : IsClosed (rankProjectionSet m n) := by
    rw [hchar]
    exact (isClosed_eq ContinuousLinearMap.adjoint.continuous continuous_id).inter
      ((isClosed_eq (continuous_id.mul continuous_id) continuous_id).inter
        (isClosed_eq tr.continuous_of_finiteDimensional continuous_const))
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨hclosed, (isCompact_closedBall (0 : Euclidean n →L[ℝ] Euclidean n) 1).isBounded.subset ?_⟩
  intro P hP
  have hp : IsStarProjection P := ⟨hP.2.1, hP.1⟩
  obtain ⟨_, hEq⟩ := isStarProjection_iff_eq_starProjection_range.mp hp
  have hn : ‖P‖ ≤ 1 := calc
    ‖P‖ = ‖P.range.starProjection‖ := congrArg norm hEq
    _ ≤ 1 := P.range.starProjection_norm_le
  simpa only [mem_closedBall, dist_zero_right] using hn

end Preiss
