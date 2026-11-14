import Preiss.Analysis.GaussianVague
import Preiss.Uniform.MomentEstimates
import Mathlib.Tactic

/-! Gaussian moment evaluations under vague convergence of unit-uniform measures. -/

open MeasureTheory Filter
open scoped Topology BigOperators
namespace Preiss
variable {n m : ℕ}

theorem vague_gaussianMomentForm_apply (hm : 0 < m)
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, IsUnitUniform m (μ i)) (hν : IsUnitUniform m ν)
    (hlim : Measure.WeaklyConverges μ ν)
    (k : ℕ) (s : ℝ) (hs : 0 < s) (u : Fin k → Euclidean n) :
    Tendsto (fun i => gaussianMomentForm (μ i) k s u) atTop
      (𝓝 (gaussianMomentForm ν k s u)) := by
  let P : MvPolynomial (Fin n) ℝ :=
    ∏ i : Fin k, ∑ j : Fin n, MvPolynomial.C (u i j) * MvPolynomial.X j
  have heval (z : Euclidean n) :
      MvPolynomial.eval (fun j => z j) P = ∏ i, inner ℝ z (u i) := by
    dsimp [P]
    rw [MvPolynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i _
    change MvPolynomial.eval (fun j => z j)
      (∑ j : Fin n, MvPolynomial.C (u i j) * MvPolynomial.X j) =
        ∑ j : Fin n, u i j * z j
    simp
  let c := (2 * s) ^ k / (k.factorial : ℝ) *
    (Real.Gamma ((m : ℝ) / 2 + 1) * s ^ (-((m : ℝ) / 2)))⁻¹
  have hform (ρ : Measure (Euclidean n)) (hρ : IsUnitUniform m ρ) :
      gaussianMomentForm ρ k s u =
        c * ∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-s * ‖z‖^2) ∂ρ := by
    rw [gaussianMomentForm_apply ρ k s (integrable_gaussianMomentKernel ρ hm hρ k s hs)]
    change ((2 * s) ^ k / (k.factorial : ℝ) * (gaussianMass ρ s)⁻¹) *
      (∫ z, (∏ i, inner ℝ z (u i)) * Real.exp (-s * ‖z‖^2) ∂ρ) = _
    rw [gaussianMass_unitUniform ρ hm hρ s hs]
    simp only [heval, c]
  have h := vague_integral_polynomial_mul_gaussian μ ν (fun i => (hμ i).1) hν.1
    hlim 1 (m : ℝ) (fun i => IsUnitUniform.hasPolynomialGrowthBound _ (hμ i))
    (IsUnitUniform.hasPolynomialGrowthBound ν hν) P s hs
  have hseq : (fun i => gaussianMomentForm (μ i) k s u) =
      fun i => c * ∫ z, MvPolynomial.eval (fun j => z j) P *
        Real.exp (-s * ‖z‖^2) ∂μ i := funext fun i => hform _ (hμ i)
  rw [hseq, hform ν hν]
  exact h.const_mul c

end Preiss
