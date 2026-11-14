module
public import Preiss.Analysis.MultilinearSymmetrization
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Tactic

@[expose] public section
open scoped BigOperators
namespace Preiss
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem symmetricMultilinear_eq_zero_of_diagonal {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) (u : Fin k → E), A (u ∘ σ) = A u)
    (hdiag : ∀ x : E, A (fun _ => x) = 0) : A = 0 := by
  classical
  ext u
  change A u = 0
  have h := A.iteratedFDeriv_comp_diagonal (0 : E) u
  have hfun : (fun x : E => A (fun _ => x)) = fun _ => (0 : F) := funext hdiag
  rw [hfun] at h
  have hσ (σ : Equiv.Perm (Fin k)) : A (fun i => u (σ i)) = A u := hsym σ u
  have hz : (Fintype.card (Equiv.Perm (Fin k)) : ℝ) • A u = 0 := by
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, ContinuousMultilinearMap.zero_apply,
      hσ, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul] using h.symm
  exact (smul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end Preiss
