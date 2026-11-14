module
public import Preiss.Uniform.MomentTrace
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! # Derivatives of normalized polynomial Gaussian integrals -/

@[expose] public section
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem hasDerivAt_normalized_polynomial_gaussian_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (P : MvPolynomial (Fin n) ℝ) (s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun t => (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-t * ‖z‖^2) ∂μ) /
        gaussianMass μ t)
      (((m : ℝ) / (2*s)) *
          ((∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖^2) ∂μ) /
            gaussianMass μ s) -
        (∫ z, ‖z‖^2 * MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖^2) ∂μ) /
          gaussianMass μ s) s := by
  have hg := IsUnitUniform.hasPolynomialGrowthBound μ hμ
  have hN := hasDerivAt_integral_polynomial_gaussian_of_ball_bound μ 1 (m : ℝ)
    hg.1 hg.2.2 P s hs
  have hI : HasDerivAt (gaussianMass μ)
      (-((m : ℝ) / (2*s)) * gaussianMass μ s) s := by
    have h := hasDerivAt_integral_polynomial_gaussian_of_ball_bound μ 1 (m : ℝ)
      hg.1 hg.2.2 (1 : MvPolynomial (Fin n) ℝ) s hs
    simp only [map_one, mul_one, one_mul] at h
    rw [integral_norm_sq_gaussian_unitUniform μ hm hμ s hs] at h
    have heq : (fun t : ℝ => ∫ z, Real.exp (-t * ‖z‖^2) ∂μ) = gaussianMass μ := rfl
    rw [← heq]
    simpa only [gaussianMass, neg_mul] using h
  have hmass : gaussianMass μ s ≠ 0 := by
    rw [gaussianMass_unitUniform μ hm hμ s hs]
    exact (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs _)).ne'
  convert! hN.div hI hmass using 1
  field_simp [hmass, hs.ne']
  <;> ring

theorem hasDerivAt_normalized_centered_gaussian_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (b w : Euclidean n) (s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun t => (∫ z, inner ℝ (z-b) w * Real.exp (-t * ‖z‖^2) ∂μ) / gaussianMass μ t)
      (((m : ℝ) / (2*s)) *
          ((∫ z, inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ) / gaussianMass μ s) -
        (∫ z, ‖z‖^2 * inner ℝ (z-b) w * Real.exp (-s * ‖z‖^2) ∂μ) /
          gaussianMass μ s) s := by
  let P : MvPolynomial (Fin n) ℝ :=
    (∑ j : Fin n, MvPolynomial.C (w j) * MvPolynomial.X j) - MvPolynomial.C (inner ℝ b w)
  have heval (z : Euclidean n) : MvPolynomial.eval (fun j => z j) P = inner ℝ (z-b) w := by
    rw [inner_sub_left]
    change MvPolynomial.eval (fun j => z j) P = (∑ j : Fin n, w j * z j) - inner ℝ b w
    simp [P]
  simpa only [heval] using hasDerivAt_normalized_polynomial_gaussian_unitUniform μ hm hμ P s hs

end Preiss
