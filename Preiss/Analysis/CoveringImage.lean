module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic.NormNum

/-! # Image measure estimates from buffered disjoint ball coverings -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
noncomputable section
namespace Preiss


theorem measure_image_le_mul_of_ball_image_bounds
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (C : Set X)
    (K : ℝ≥0∞) (R : ℝ)
    (hlocal : ∀ x ∈ C, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ν (f '' (C ∩ ball x (5 * r))) ≤ K * μ (ball x r)) :
    ν (f '' C) ≤ K * μ univ := by
  classical
  choose r hrpos hrbound hbound using fun x : C ↦ hlocal x x.property
  obtain ⟨U, _, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball (univ : Set C)
      (fun x : C ↦ (x : X)) r R (fun x _ ↦ hrbound x) 5 (by norm_num)
  have hcount : U.Countable := hdisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun x _ ↦ ⟨x, mem_ball_self (hrpos x)⟩)
  letI : Countable U := hcount.to_subtype
  have hpair : Pairwise (fun u v : U ↦ Disjoint
      (ball ((u : C) : X) (r u)) (ball ((v : C) : X) (r v))) := by
    intro u v huv
    exact hdisj u.property v.property (fun hh ↦ huv (Subtype.ext hh))
  have hmass : (∑' u : U, μ (ball ((u : C) : X) (r u))) ≤ μ univ := by
    rw [← measure_iUnion hpair (fun _ ↦ isOpen_ball.measurableSet)]
    exact measure_mono (subset_univ _)
  have hsub : f '' C ⊆ ⋃ u : U, f '' (C ∩ ball ((u : C) : X) (5 * r u)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hij⟩ := hcover (⟨x, hx⟩ : C) (mem_univ _)
    refine mem_iUnion.mpr ⟨⟨j, hj⟩, x, ⟨hx, ?_⟩, rfl⟩
    exact hij (mem_ball_self (hrpos ⟨x, hx⟩))
  calc
    ν (f '' C) ≤ ν (⋃ u : U, f '' (C ∩ ball ((u : C) : X) (5 * r u))) := measure_mono hsub
    _ ≤ ∑' u : U, ν (f '' (C ∩ ball ((u : C) : X) (5 * r u))) := measure_iUnion_le _
    _ ≤ ∑' u : U, K * μ (ball ((u : C) : X) (r u)) :=
      ENNReal.tsum_le_tsum fun u ↦ hbound u
    _ = K * (∑' u : U, μ (ball ((u : C) : X) (r u))) := ENNReal.tsum_mul_left
    _ ≤ K * μ univ := mul_le_mul_of_nonneg_left hmass bot_le

end Preiss
