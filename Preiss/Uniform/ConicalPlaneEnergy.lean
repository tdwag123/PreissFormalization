module

public import Preiss.Uniform.Radial
public import Preiss.Uniform.BallBoundary
public import Preiss.Geometry.PlaneDistance
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity

/-! # Gaussian plane energy from conical ball energy -/

@[expose] public section
open MeasureTheory Metric Set
namespace Preiss
variable {n m : ℕ}

theorem conical_gaussian_planeEnergy_eq_ball
    (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (V : Plane m n) :
    (∫ z, Real.exp (-‖z‖ ^ 2) * (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ) =
      Real.Gamma (((m : ℝ) + 2) / 2 + 1) *
        ∫ z in ball 0 1, (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ := by
  letI : μ.Regular := hμ.1
  have hcont := (continuous_infDist_pt (V.1 : Set (Euclidean n))).pow 2
  have hhom : ∀ r > 0, ∀ z : Euclidean n,
      (infDist (r • z) (V.1 : Set (Euclidean n))) ^ 2 =
        r ^ (2 : ℝ) * (infDist z (V.1 : Set (Euclidean n))) ^ 2 := by
    intro r hr z
    rw [infDist_smul_plane, Real.norm_of_nonneg hr.le, mul_pow, Real.rpow_two]
  have h := (integral_gaussian_mul_homogeneous μ hμ.1 hc _ hcont.measurable
    (fun z => sq_nonneg _) 2 (by positivity) hhom
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _))).2
  rw [← setIntegral_congr_set (unitUniform_ball_ae_eq_closedBall hμ hμ.2.1 zero_lt_one)] at h
  exact h


end Preiss
