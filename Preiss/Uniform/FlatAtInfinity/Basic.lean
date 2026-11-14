import Preiss.Uniform.MomentCoefficients
import Preiss.Uniform.Defs
import Preiss.Tangent.Defs
import Preiss.Geometry.Projections
import Preiss.Geometry.PlaneMeasure
import Preiss.Analysis.BilinearTrace
import Preiss.Geometry.NormalCoordinates
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open MeasureTheory Metric
namespace Preiss
variable {n m : ℕ}

/-- An explicit normal vector representing the first Taylor coefficient. -/
def IsFirstMomentNormalVector (B : MomentCoefficientFamily n) (V : Plane m n)
    (b : V.1ᗮ) : Prop :=
  ∀ x : Euclidean n, B 1 1 (fun _ => x) = 2 * inner ℝ (b : Euclidean n) x

/-- The first coefficient has a normal Riesz representative whenever its restriction
to the plane vanishes. This lemma does not assume a moment expansion or a blow-down. -/
theorem exists_firstMomentNormalVector_of_restrict_eq_zero
    (B : MomentCoefficientFamily n) (V : Plane m n)
    (hzero : ∀ u : V.1, B 1 1 (fun _ => (u : Euclidean n)) = 0) :
    ∃ b : V.1ᗮ, IsFirstMomentNormalVector B V b := by
  let A : Euclidean n →L[ℝ] ℝ :=
    continuousMultilinearCurryFin1 ℝ (Euclidean n) ℝ (B 1 1)
  have hA (x : Euclidean n) : A x = B 1 1 (fun _ => x) := by
    dsimp only [A]
    rw [continuousMultilinearCurryFin1_apply]
    congr 1
  let L : Euclidean n →L[ℝ] ℝ := (1 / 2 : ℝ) • A
  have hL : ∀ x ∈ V.1, L x = 0 := by
    intro x hx
    have hz := hzero ⟨x, hx⟩
    simp only [L, ContinuousLinearMap.smul_apply, smul_eq_mul, hA, hz, mul_zero]
  obtain ⟨b, hb⟩ := exists_orthogonal_representative V.1 L hL
  refine ⟨b, ?_⟩
  intro x
  have h := hb x
  simp only [L, ContinuousLinearMap.smul_apply, smul_eq_mul, hA] at h
  linarith

theorem evenMomentCoefficient_eq_projection_norm
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (j : ℕ) (hj : 0 < j) (x : Euclidean n) :
    B (2 * j) j (fun _ => x) = ‖proj V x‖ ^ (2 * j) := by
  sorry

theorem oddMomentCoefficient_restrict_plane_eq_zero
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (j : ℕ) (hj : 0 < j) (u : Fin (2 * j - 1) → V.1) :
    B (2 * j - 1) j (fun i => (u i : Euclidean n)) = 0 := by
  sorry

theorem exists_firstMomentNormalVector
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V)) :
    ∃ b : V.1ᗮ, IsFirstMomentNormalVector B V b := by
  sorry

theorem support_normal_sq_eq_inner
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (x : Euclidean n) (hx : x ∈ μ.support) :
    ‖x - proj V x‖ ^ 2 = 2 * inner ℝ (b : Euclidean n) x ∧
    ‖x - proj V x - (b : Euclidean n)‖ = ‖b‖ ∧
    ‖x - proj V x‖ ≤ 2 * ‖b‖ := by
  sorry

theorem exists_uniform_dist_plane_support_bound
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V)) :
    ∃ R : ℝ, 0 < R ∧ ∀ v : V.1, infDist (v : Euclidean n) μ.support < R := by
  sorry

theorem trace_secondMomentCoefficient_normal_eq
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b) :
    bilinearTrace (restrictBilinear (momentBilinear (B 2 2)) V.1ᗮ) = 8 * ‖b‖ ^ 2 := by
  sorry

end Preiss
