module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

/-! # Finite-basis expansions and limits of weighted integrals -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Preiss

theorem bilinear_diagonal_eq_sum_orthonormalBasis
    {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E →L[ℝ] F) (v : E) :
    A v v = ∑ i, ∑ j, (inner ℝ (e i) v * inner ℝ (e j) v) • A (e i) (e j) := by
  classical
  conv_lhs => rw [← e.sum_repr v]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul, OrthonormalBasis.repr_apply_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem tendsto_weighted_integral_finite_linear_combination
    {X I J : Type*} [MeasurableSpace X] [Fintype J]
    (μ : Measure X) (l : Filter I) (weight : I → X → ℝ) (scale : I → ℝ)
    (f : J → X → ℝ) (a L : J → ℝ)
    (hint : ∀ j, ∀ᶠ i in l, Integrable (fun x => weight i x * f j x) μ)
    (hlim : ∀ j, Tendsto (fun i => scale i * ∫ x, weight i x * f j x ∂μ) l (𝓝 (L j))) :
    (∀ᶠ i in l, Integrable (fun x => weight i x * ∑ j, a j * f j x) μ) ∧
    Tendsto (fun i => scale i * ∫ x, weight i x * ∑ j, a j * f j x ∂μ)
      l (𝓝 (∑ j, a j * L j)) := by
  classical
  have heq (i : I) : (fun x => weight i x * ∑ j, a j * f j x) =
      (fun x => ∑ j, a j * (weight i x * f j x)) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hall : ∀ᶠ i in l, ∀ j, Integrable (fun x => weight i x * f j x) μ :=
    eventually_all.mpr hint
  constructor
  · filter_upwards [hall] with i hi
    rw [heq]
    exact integrable_finsetSum _ (fun j _ => (hi j).const_mul (a j))
  · have ht := tendsto_finsetSum Finset.univ (fun j _ => (hlim j).const_mul (a j))
    apply ht.congr'
    filter_upwards [hall] with i hi
    rw [heq, integral_finsetSum _ (fun j _ => (hi j).const_mul (a j))]
    simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end Preiss
