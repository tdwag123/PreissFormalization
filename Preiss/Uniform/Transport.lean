module

public import Preiss.Uniform.Scaling
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Uniform measures under isometric identifications

The embedding is returned as data by dimension reduction and is retained in
all pushforward, support and blow-up identities.
-/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n k : ℕ}

/-- A04, generalized to any linear isometric embedding of Euclidean spaces. -/
theorem uniform_hyperplane_transport (L : Euclidean k →ₗᵢ[ℝ] Euclidean n)
    (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ)
    (hsupp : μ.support ⊆ Set.range L) :
    ∃ ν : Measure (Euclidean k), IsUnitUniform m ν ∧ ν.map L = μ ∧
      L '' ν.support = μ.support ∧
      ∀ (x : Euclidean k) (r : ℝ), 0 < r →
        (dimensionalBlowup m ν x r).map L = dimensionalBlowup m μ (L x) r := by
  sorry

/-- The version preserving an arbitrary fixed positive ball constant. -/
theorem uniformWithConstant_transport (L : Euclidean k →ₗᵢ[ℝ] Euclidean n)
    (μ : Measure (Euclidean n)) {q : ℝ} (hμ : IsUniformWithConstant m q μ)
    (hsupp : μ.support ⊆ Set.range L) :
    ∃ ν : Measure (Euclidean k), IsUniformWithConstant m q ν ∧ ν.map L = μ ∧
      L '' ν.support = μ.support ∧
      ∀ (x : Euclidean k) (r : ℝ), 0 < r →
        (dimensionalBlowup m ν x r).map L = dimensionalBlowup m μ (L x) r := by
  sorry

end Preiss
