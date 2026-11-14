module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic

open Filter Asymptotics
open scoped Topology
@[expose] public section
namespace Preiss
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_taylor_jets_of_analyticAt_zero (f : ℝ → F) (hf : AnalyticAt ℝ f 0) :
    ∃ A : ℕ → F, A 0 = f 0 ∧ ∀ q : ℕ,
      IsLittleO (𝓝 (0 : ℝ))
        (fun s => f s - ∑ i ∈ Finset.range (q + 1), s ^ i • A i)
        (fun s : ℝ => s ^ q) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨fun i => p i (fun _ => 1), hp.coeff_zero _, ?_⟩
  intro q
  have heval (i : ℕ) (s : ℝ) : p i (fun _ => s) = s ^ i • p i (fun _ => 1) := by
    simpa using (p i).map_smul_univ (fun _ => s) (fun _ => (1 : ℝ))
  have hsum (s : ℝ) : p.partialSum (q + 1) s =
      ∑ i ∈ Finset.range (q + 1), s ^ i • p i (fun _ => 1) := by
    unfold FormalMultilinearSeries.partialSum
    apply Finset.sum_congr rfl
    intro i _
    exact heval i s
  have ht := (hp.isBigO_sub_partialSum_pow (q + 1)).trans_isLittleO
    (isLittleO_norm_pow_norm_pow (E' := ℝ) (Nat.lt_succ_self q))
  have ht' : IsLittleO (𝓝 (0 : ℝ))
      (fun s => f s - ∑ i ∈ Finset.range (q + 1), s ^ i • p i (fun _ => 1))
      (fun s : ℝ => ‖s ^ q‖) := by
    simpa only [zero_add, hsum, norm_pow] using ht
  exact isLittleO_norm_right.mp ht'

theorem exists_positive_taylor_jets_of_analyticAt_zero (f : ℝ → F)
    (hf : AnalyticAt ℝ f 0) (hzero : f 0 = 0) :
    ∃ A : ℕ → F, ∀ q : ℕ,
      IsLittleO (𝓝 (0 : ℝ))
        (fun s => f s - ∑ i ∈ Finset.range q, s ^ (i + 1) • A (i + 1))
        (fun s : ℝ => s ^ q) := by
  obtain ⟨A, hA, hjet⟩ := exists_taylor_jets_of_analyticAt_zero f hf
  refine ⟨A, fun q => ?_⟩
  have ht := hjet q
  simpa only [Finset.sum_range_succ', hA, hzero, smul_zero, add_zero] using ht

end Preiss
