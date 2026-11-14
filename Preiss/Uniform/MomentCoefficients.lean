module

public import Preiss.Uniform.MomentForms
public import Mathlib.Analysis.Asymptotics.Defs

/-! # Explicit Gaussian moment coefficient families

Expansion data are passed explicitly. No coefficient is chosen from an
unproved existence theorem. Degree vanishings and support identities are
separate results in `MomentExpansion`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Preiss

abbrev MomentCoefficientFamily (n : ℕ) := (k j : ℕ) → MomentForm n k

noncomputable def momentTaylorPolynomial {n : ℕ} (B : MomentCoefficientFamily n)
    (k q : ℕ) (s : ℝ) : MomentForm n k :=
  ∑ j ∈ Finset.range q, (s ^ (j + 1) / ((j + 1).factorial : ℝ)) • B k (j + 1)

/-- Symmetric coefficients and operator-norm Taylor expansions along positive scales. -/
def IsMomentExpansion {n : ℕ} (μ : Measure (Euclidean n))
    (B : MomentCoefficientFamily n) : Prop :=
  (∀ k j : ℕ, ∀ σ : Equiv.Perm (Fin k), ∀ u : Fin k → Euclidean n,
    B k j (u ∘ σ) = B k j u) ∧
  ∀ k : ℕ, 0 < k → ∀ q : ℕ, 0 < q →
    Asymptotics.IsLittleO (nhdsWithin 0 (Ioi 0))
      (fun s : ℝ => gaussianMomentForm μ k s - momentTaylorPolynomial B k q s)
      (fun s : ℝ => s ^ q)

end Preiss
