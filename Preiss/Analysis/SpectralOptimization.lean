module
public import Preiss.Geometry.Projections
public import Preiss.Analysis.BilinearTrace
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section
namespace Preiss
variable {n m : ℕ}

theorem trace_orthogonalComplement_minimized_topEigenspace
    (A : Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ)
    (hA : ∀ u v, A u v = A v u) (hpos : ∀ u, 0 ≤ A u u) (hmn : m ≤ n) :
    ∃ (e : OrthonormalBasis (Fin n) ℝ (Euclidean n)) (α : Fin n → ℝ)
      (V : Plane m n), Antitone α ∧ (∀ i, 0 ≤ α i) ∧
      (∀ i x, A (e i) x = α i * inner ℝ (e i) x) ∧
      V.1 = Submodule.span ℝ (Set.range (fun i : Fin m => e (Fin.castLE hmn i))) ∧
      ∀ W : Plane m n,
        bilinearTrace (restrictBilinear A V.1ᗮ) ≤ bilinearTrace (restrictBilinear A W.1ᗮ) := by
  sorry

end Preiss
