module

public import Preiss.Geometry.Planes
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Isometric parametrizations of linear planes -/

@[expose] public section
namespace Preiss
variable {m n : ℕ}

theorem exists_linearIsometry_range_plane (V : Plane m n) :
    ∃ L : Euclidean m →ₗᵢ[ℝ] Euclidean n, Set.range L = (V.1 : Set (Euclidean n)) := by
  classical
  let e : Euclidean m ≃ₗᵢ[ℝ] V.1 :=
    ((stdOrthonormalBasis ℝ V.1).reindex (finCongr V.property)).repr.symm
  let L : Euclidean m →ₗᵢ[ℝ] Euclidean n := V.1.subtypeₗᵢ.comp e.toLinearIsometry
  refine ⟨L, ?_⟩
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (e z).property
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    change ((e (e.symm ⟨x, hx⟩) : V.1) : Euclidean n) = x
    simp

end Preiss
