module
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Data.Fin.VecNotation
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

theorem symmetricTrilinear_diagonal_add
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → E), A (u ∘ σ) = A u)
    (p q : E) :
    A ![p+q,p+q,p+q] = A ![p,p,p] + 3 * A ![p,p,q] +
      3 * A ![p,q,q] + A ![q,q,q] := by
  have add₁ (a b y z : E) : A ![a+b,y,z] = A ![a,y,z] + A ![b,y,z] := by
    change (A.curryLeft (a+b)) ![y,z] =
      (A.curryLeft a) ![y,z] + (A.curryLeft b) ![y,z]
    simp only [map_add, ContinuousMultilinearMap.add_apply]
  have add₂ (x a b z : E) : A ![x,a+b,z] = A ![x,a,z] + A ![x,b,z] := by
    change ((A.curryLeft x).curryLeft (a+b)) ![z] =
      ((A.curryLeft x).curryLeft a) ![z] + ((A.curryLeft x).curryLeft b) ![z]
    simp only [map_add, ContinuousMultilinearMap.add_apply]
  have add₃ (x y a b : E) : A ![x,y,a+b] = A ![x,y,a] + A ![x,y,b] := by
    change (((A.curryLeft x).curryLeft y).curryLeft (a+b)) ![] =
      (((A.curryLeft x).curryLeft y).curryLeft a) ![] +
        (((A.curryLeft x).curryLeft y).curryLeft b) ![]
    simp only [map_add, ContinuousMultilinearMap.add_apply]
  have swap₁ (a b c : E) : A ![b,a,c] = A ![a,b,c] := by
    have hperm : (![a,b,c] ∘ Equiv.swap (0 : Fin 3) 1) = ![b,a,c] := by
      ext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [hperm] using hsym (Equiv.swap (0 : Fin 3) 1) ![a,b,c]
  have swap₂ (a b c : E) : A ![a,c,b] = A ![a,b,c] := by
    have hperm : (![a,b,c] ∘ Equiv.swap (1 : Fin 3) 2) = ![a,c,b] := by
      ext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [hperm] using hsym (Equiv.swap (1 : Fin 3) 2) ![a,b,c]
  have h₁ := swap₂ p p q
  have h₂ := (swap₁ p q p).trans h₁
  have h₃ := swap₁ p q q
  have h₄ := (swap₂ q p q).trans h₃
  simp only [add₁, add₂, add₃, h₁, h₂, h₃, h₄]
  ring


end Preiss
