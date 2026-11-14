module

public import Preiss.Uniform.Moments
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Continuous multilinear Gaussian moments

The moment form is a Bochner integral in the Banach space of continuous
multilinear maps. Thus its definition requires no choice of an unproved
existence theorem. Evaluation identities state their integrability assumption.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators

namespace Preiss
variable {n : ℕ}

abbrev MomentForm (n k : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclidean n) ℝ

noncomputable def momentBilinear (A : MomentForm n 2) :
    Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ (Euclidean n) ℝ).toContinuousLinearEquiv
    .toContinuousLinearMap.comp A.curryLeft

/-- Product of the continuous linear functionals given by inner product with `z`. -/
noncomputable def momentKernel (k : ℕ) (z : Euclidean n) : MomentForm n k :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
    (fun _ => innerSL ℝ z)

noncomputable def gaussianMass (μ : Measure (Euclidean n)) (s : ℝ) : ℝ :=
  ∫ z, Real.exp (-s * ‖z‖ ^ 2) ∂μ

/-- The integral is taken in the space of continuous multilinear forms. -/
noncomputable def gaussianMomentForm (μ : Measure (Euclidean n)) (k : ℕ)
    (s : ℝ) : MomentForm n k :=
  ((2 * s) ^ k / (Nat.factorial k : ℝ) * (gaussianMass μ s)⁻¹) •
    ∫ z, Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z ∂μ

theorem gaussianMomentForm_apply (μ : Measure (Euclidean n)) (k : ℕ) (s : ℝ)
    (hint : Integrable (fun z => Real.exp (-s * ‖z‖ ^ 2) • momentKernel k z) μ)
    (u : Fin k → Euclidean n) :
    gaussianMomentForm μ k s u = gaussianMoment μ k s u := by
  sorry

theorem gaussianMomentForm_permute (μ : Measure (Euclidean n)) (k : ℕ) (s : ℝ)
    (σ : Equiv.Perm (Fin k)) (u : Fin k → Euclidean n) :
    gaussianMomentForm μ k s (u ∘ σ) = gaussianMomentForm μ k s u := by
  sorry

end Preiss
