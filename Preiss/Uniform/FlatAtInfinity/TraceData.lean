import Preiss.Uniform.FlatAtInfinity.Basic
import Mathlib.Data.Fin.VecNotation

open MeasureTheory
namespace Preiss
variable {n m : ℕ}

abbrev RigidityOmega (V : Plane m n) := V.1 →L[ℝ] V.1 →L[ℝ] V.1ᗮ
abbrev RigidityAdjustedForm (V : Plane m n) := V.1 →L[ℝ] V.1 →L[ℝ] ℝ

/-- Exact defining identity for a typed normal-valued symmetric bilinear map. -/
def IsRigidityOmega (B : MomentCoefficientFamily n) (V : Plane m n) (b : V.1ᗮ)
    (ω : RigidityOmega V) : Prop :=
  (∀ u v, ω u v = ω v u) ∧
  ∀ u v : V.1, ∀ w : V.1ᗮ,
    inner ℝ (ω u v) w =
      3 * B 3 2 ![(u : Euclidean n), (v : Euclidean n), (w : Euclidean n)] -
        4 * inner ℝ u v * inner ℝ b w

/-- Exact defining identity for the adjusted real bilinear form. -/
def IsRigidityAdjustedForm (B : MomentCoefficientFamily n) (V : Plane m n)
    (b : V.1ᗮ) (ω : RigidityOmega V) (A : RigidityAdjustedForm V) : Prop :=
  (∀ u v, A u v = A v u) ∧
  ∀ u v : V.1,
    A u v = B 2 2 ![(u : Euclidean n), (v : Euclidean n)] + inner ℝ (ω u v) b

theorem exists_rigidityOmega_and_adjustedForm
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b) :
    ∃ ω : RigidityOmega V, IsRigidityOmega B V b ω ∧
      ∃ A : RigidityAdjustedForm V, IsRigidityAdjustedForm B V b ω A := by
  sorry

end Preiss
