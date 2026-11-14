import Preiss.Uniform.FlatAtInfinity.Basic
import Preiss.Uniform.MomentExpansion
import Mathlib.Tactic

/-! Assembly validation only: the intended odd/even coefficient identities and
bounded-tube theorem are explicit parameters. These checks do not discharge those
prerequisites and are not the canonical rigidity statements. -/
open MeasureTheory Metric
namespace Preiss
variable {n m : ℕ}

theorem firstMomentNormalVector_assembly
    (B : MomentCoefficientFamily n) (V : Plane m n)
    (hodd : ∀ (j : ℕ), 0 < j → ∀ u : Fin (2 * j - 1) → V.1,
      B (2 * j - 1) j (fun i => (u i : Euclidean n)) = 0) :
    ∃ b : V.1ᗮ, IsFirstMomentNormalVector B V b := by
  apply exists_firstMomentNormalVector_of_restrict_eq_zero B V
  intro u
  simpa using hodd 1 zero_lt_one (fun _ => u)

theorem supportNormal_assembly
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n)
    (heven : ∀ (j : ℕ), 0 < j → ∀ x : Euclidean n,
      B (2 * j) j (fun _ => x) = ‖proj V x‖ ^ (2 * j))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (x : Euclidean n) (hx : x ∈ μ.support) :
    ‖x - proj V x‖ ^ 2 = 2 * inner ℝ (b : Euclidean n) x ∧
      ‖x - proj V x - (b : Euclidean n)‖ = ‖b‖ ∧
      ‖x - proj V x‖ ≤ 2 * ‖b‖ := by
  have hs := sum_gaussianMomentCoefficient_eq_norm_pow μ hm hμ B hB 1 zero_lt_one x hx
  have he : B 2 1 (fun _ => x) = ‖proj V x‖ ^ 2 := by simpa using heven 1 zero_lt_one x
  norm_num [Finset.sum_range_succ] at hs
  rw [he, hb x] at hs
  exact normal_coordinates_of_quadratic_identity V.1 b x hs

theorem planeToSupportBound_assembly
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n)
    (heven : ∀ (j : ℕ), 0 < j → ∀ x : Euclidean n,
      B (2 * j) j (fun _ => x) = ‖proj V x‖ ^ (2 * j))
    (hodd : ∀ (j : ℕ), 0 < j → ∀ u : Fin (2 * j - 1) → V.1,
      B (2 * j - 1) j (fun i => (u i : Euclidean n)) = 0)
    (hholes : ∀ M : ℝ, 0 ≤ M → (∀ x ∈ μ.support, ‖x - proj V x‖ ≤ M) →
      ∃ R : ℝ, 0 < R ∧ ∀ v : V.1, infDist (v : Euclidean n) μ.support < R) :
    ∃ R : ℝ, 0 < R ∧ ∀ v : V.1, infDist (v : Euclidean n) μ.support < R := by
  obtain ⟨b, hb⟩ := firstMomentNormalVector_assembly B V hodd
  apply hholes (2 * ‖b‖) (by positivity)
  intro x hx
  exact (supportNormal_assembly μ hm hμ B hB V heven b hb x hx).2.2

#print axioms firstMomentNormalVector_assembly
#print axioms supportNormal_assembly
#print axioms planeToSupportBound_assembly
end Preiss
