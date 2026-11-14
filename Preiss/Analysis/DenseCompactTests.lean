module

public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Tactic.Choose

/-! # Countable compact tests with common-support uniform approximation

The construction uses only locally compact, second-countable Hausdorff topology.
Cutoffs and approximating tests belong to the same enumerated family.
-/

@[expose] public section
open Set Filter Topology
open scoped CompactlySupported
namespace Preiss
variable {X : Type*} [TopologicalSpace X]

/-- A countable family that approximates each compact test with one common compact support. -/
structure DenseCompactTestFamily (X : Type*) [TopologicalSpace X] where
  tests : ℕ → C_c(X, ℝ)
  cutoffs : ∀ K : Set X, IsCompact K → ∃ j,
    (∀ x, 0 ≤ tests j x) ∧ ∀ x ∈ K, 1 ≤ tests j x
  approximation : ∀ f : C_c(X, ℝ), ∃ K : Set X, IsCompact K ∧ tsupport f ⊆ K ∧
    ∀ ε : ℝ, 0 < ε → ∃ j, tsupport (tests j) ⊆ K ∧
      ∀ x, |tests j x - f x| < ε

theorem dense_continuousMap_uniform_approximation
    (g : ℕ → C(X, ℝ)) (hg : DenseRange g) (f : C(X, ℝ))
    (K : Set X) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ j, ∀ x ∈ K, |g j x - f x| < ε := by
  have hb : (𝓝 f).HasBasis (fun p : Set X × ℝ => IsCompact p.1 ∧ 0 < p.2)
      (fun p => {g : C(X, ℝ) | ∀ x ∈ p.1, dist (g x) (f x) < p.2}) :=
    nhds_basis_uniformity Metric.uniformity_basis_dist.compactConvergenceUniformity
  obtain ⟨j, hj⟩ := hg.mem_nhds (hb.mem_of_mem (i := (K, ε)) ⟨hK, hε⟩)
  exact ⟨j, fun x hx => by simpa only [Real.dist_eq] using hj x hx⟩

theorem exists_denseCompactTestFamily [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] : Nonempty (DenseCompactTestFamily X) := by
  classical
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  let K : CompactExhaustion X := default
  have hcut (N : ℕ) : ∃ u : C_c(X, ℝ), EqOn u 1 (K N) ∧
      tsupport u ⊆ K (N + 1) ∧ ∀ x, u x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨v, hvone, hvcompact, hvsupport, hvbounds⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen (K.isCompact N)
        isOpen_interior (K.subset_interior_succ N)
    exact ⟨⟨v, hvcompact⟩, hvone, hvsupport.trans interior_subset, hvbounds⟩
  choose u huone husupport hubounds using hcut
  let T (N : ℕ) : ℕ → C_c(X, ℝ)
    | 0 => u N
    | j + 1 => g j • u N
  let tests (i : ℕ) := T (Nat.unpair i).1 (Nat.unpair i).2
  have htest0 (N : ℕ) : tests (Nat.pair N 0) = u N := by simp [tests, T]
  have htestsucc (N j : ℕ) : tests (Nat.pair N (j + 1)) = g j • u N := by
    simp [tests, T]
  refine ⟨⟨tests, ?_, ?_⟩⟩
  · intro S hS
    obtain ⟨N, hSN⟩ := K.exists_superset_of_isCompact hS
    refine ⟨Nat.pair N 0, ?_, ?_⟩
    · intro x
      rw [htest0]
      exact (hubounds N x).1
    · intro x hx
      rw [htest0]
      exact (huone N (hSN hx)).ge
  · intro f
    obtain ⟨N, hfN⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
    have hfK : tsupport f ⊆ K (N + 1) := hfN.trans (K.subset (Nat.le_succ N))
    refine ⟨K (N + 1), K.isCompact _, hfK, ?_⟩
    intro ε hε
    obtain ⟨j, hj⟩ := dense_continuousMap_uniform_approximation g hg f.toContinuousMap
      (K (N + 1)) (K.isCompact _) ε hε
    refine ⟨Nat.pair N (j + 1), ?_, ?_⟩
    · rw [htestsucc]
      exact (tsupport_smul_subset_right (g j) (u N)).trans (husupport N)
    · intro x
      rw [htestsucc]
      change |g j x * u N x - f x| < ε
      by_cases hx : x ∈ K (N + 1)
      · have huf : u N x * f x = f x := by
          by_cases hxf : x ∈ tsupport f
          · rw [huone N (hfN hxf), Pi.one_apply, one_mul]
          · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero]
        have heq : g j x * u N x - f x = u N x * (g j x - f x) := by
          rw [mul_sub, huf, mul_comm]
        rw [heq, abs_mul, abs_of_nonneg (hubounds N x).1]
        calc u N x * |g j x - f x| ≤ 1 * |g j x - f x| :=
            mul_le_mul_of_nonneg_right (hubounds N x).2 (abs_nonneg _)
          _ = |g j x - f x| := one_mul _
          _ < ε := hj x hx
      · have hu0 : u N x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (husupport N h))
        have hf0 : f x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (hfK h))
        simpa only [hu0, hf0, mul_zero, sub_self, abs_zero] using hε

end Preiss
