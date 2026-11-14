module

public import Preiss.Uniform.Defs
public import Preiss.Tangent.Algebra

/-! # Uniform ball constants and changes of centre and scale

The uncentered predicate explicitly requires nonempty support. In particular,
`infDist 0 μ.support = 0` cannot accidentally admit the zero measure.
-/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- An uncentered regular uniform measure with a specified positive ball constant. -/
def IsUniformWithConstant (m : ℕ) (q : ℝ) (μ : Measure (Euclidean n)) : Prop :=
  μ.Regular ∧ μ.support.Nonempty ∧ 0 < q ∧
    ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (closedBall x r) = ENNReal.ofReal (q * r ^ m)

theorem isUnitUniform_iff_constant_one (μ : Measure (Euclidean n)) :
    IsUnitUniform m μ ↔ IsUniformWithConstant m 1 μ ∧ (0 : Euclidean n) ∈ μ.support := by
  sorry

theorem uniformWithConstant_dimensionalBlowup (μ : Measure (Euclidean n))
    {q : ℝ} (hμ : IsUniformWithConstant m q μ) (a : Euclidean n)
    {r : ℝ} (hr : 0 < r) :
    IsUniformWithConstant m q (dimensionalBlowup m μ a r) := by
  sorry

theorem isUnitUniform_dimensionalBlowup (μ : Measure (Euclidean n))
    (hμ : IsUnitUniform m μ) (a : Euclidean n) (ha : a ∈ μ.support)
    {r : ℝ} (hr : 0 < r) :
    IsUnitUniform m (dimensionalBlowup m μ a r) := by
  sorry

theorem uniformWithConstant_smul (μ : Measure (Euclidean n))
    {q c : ℝ} (hμ : IsUniformWithConstant m q μ) (hc : 0 < c) :
    IsUniformWithConstant m (c * q) (ENNReal.ofReal c • μ) := by
  sorry

end Preiss
