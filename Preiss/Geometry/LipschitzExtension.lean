module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Preiss.Geometry.Euclidean
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_lipschitz_extension_finiteDimensional
    {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (A : Set X) (f : A → Y)
    {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ F : X → Y, (∃ L : ℝ≥0, LipschitzWith L F) ∧ ∀ x : A, F x = f x := by
  classical
  let e : Y ≃L[ℝ] (Fin (Module.finrank ℝ Y) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  let F₀ : X → Fin (Module.finrank ℝ Y) → ℝ := fun x ↦
    if hx : x ∈ A then e (f ⟨x, hx⟩) else 0
  have hL := e.lipschitzWith.comp hf
  have hF : LipschitzOnWith
      (‖(e : Y →L[ℝ] (Fin (Module.finrank ℝ Y) → ℝ))‖₊ * K) F₀ A := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F₀, dite_eq_left hx, dite_eq_left hy, Function.comp_apply,
      Subtype.dist_eq] using hL.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, hg, hEq⟩ := hF.extend_pi
  refine ⟨fun x ↦ e.symm (g x), ⟨_, e.symm.lipschitzWith.comp hg⟩, ?_⟩
  intro x
  have hx : e (f x) = g x := by
    simpa only [F₀, dite_eq_left x.property] using hEq x.property
  change e.symm (g (x : X)) = f x
  rw [← hx, e.symm_apply_apply]


theorem exists_lipschitz_extension_euclidean (A : Set (Euclidean m))
    (f : A → Euclidean n) {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ F : Euclidean m → Euclidean n, (∃ L : ℝ≥0, LipschitzWith L F) ∧
      ∀ x : A, F x = f x := by
  classical
  let e : Euclidean n ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_euclideanSpace_fin, Module.finrank_fin_fun])
  let F₀ : Euclidean m → Fin n → ℝ := fun x ↦
    if hx : x ∈ A then e (f ⟨x, hx⟩) else 0
  have hL := e.lipschitzWith.comp hf
  have hF : LipschitzOnWith (‖(e : Euclidean n →L[ℝ] (Fin n → ℝ))‖₊ * K) F₀ A := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F₀, dite_eq_left hx, dite_eq_left hy, Function.comp_apply,
      Subtype.dist_eq] using hL.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, hg, hEq⟩ := hF.extend_pi
  refine ⟨fun x ↦ e.symm (g x), ⟨_, e.symm.lipschitzWith.comp hg⟩, ?_⟩
  intro x
  have hx : e (f x) = g x := by
    simpa only [F₀, dite_eq_left x.property] using hEq x.property
  change e.symm (g (x : Euclidean m)) = f x
  rw [← hx, e.symm_apply_apply]

end Preiss
