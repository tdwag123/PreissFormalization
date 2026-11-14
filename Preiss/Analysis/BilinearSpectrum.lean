module

public import Preiss.Analysis.BilinearTrace
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
open scoped BigOperators
namespace Preiss

theorem exists_ordered_spectral_representation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ x y, A x y = A y x)
    (hpos : ∀ x, 0 ≤ A x x) :
    ∃ (e : OrthonormalBasis (Fin n) ℝ E) (α : Fin n → ℝ), Antitone α ∧
      (∀ j, 0 ≤ α j) ∧ (∑ j, α j) = bilinearTrace A ∧
      ∀ x, A x x = ∑ j, α j * (inner ℝ x (e j)) ^ 2 := by
  let T : E →L[ℝ] E := InnerProductSpace.continuousLinearMapOfBilin A
  have hT (x y : E) : inner ℝ (T x) y = A x y :=
    InnerProductSpace.continuousLinearMapOfBilin_apply A x y
  have hTsym : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (T x) y = inner ℝ x (T y)
    calc
      inner ℝ (T x) y = A x y := hT x y
      _ = A y x := hsym x y
      _ = inner ℝ (T y) x := (hT y x).symm
      _ = inner ℝ x (T y) := real_inner_comm x (T y)
  let e := hTsym.eigenvectorBasis hn
  let α := hTsym.eigenvalues hn
  have heig (j : Fin n) : T (e j) = α j • e j := hTsym.apply_eigenvectorBasis hn j
  have hdiag (j : Fin n) : A (e j) (e j) = α j := by
    rw [← hT, heig]
    simp only [inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq, e.norm_eq_one,
      one_pow, mul_one]
  refine ⟨e, α, hTsym.eigenvalues_antitone hn, ?_, ?_, ?_⟩
  · intro j
    rw [← hdiag]
    exact hpos (e j)
  · rw [bilinearTrace_eq_sum_diagonal A e]
    exact Finset.sum_congr rfl (fun j _ => (hdiag j).symm)
  · intro x
    calc
      A x x = inner ℝ (T x) x := (hT x x).symm
      _ = ∑ j, inner ℝ (T x) (e j) * inner ℝ (e j) x :=
        (e.sum_inner_mul_inner (T x) x).symm
      _ = ∑ j, α j * (inner ℝ x (e j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hs' : inner ℝ (T x) (e j) = inner ℝ x (T (e j)) := hTsym x (e j)
        rw [hs', heig, inner_smul_right, real_inner_comm x (e j)]
        ring

end Preiss
