module

public import Preiss.Analysis.BallBoundary
public import Preiss.Uniform.Defs

/-! # Positive-radius uniform spheres and ball boundaries

This bridge applies also in dimension zero: only the strictly positive radius matters.
-/

@[expose] public section
open MeasureTheory Metric
namespace Preiss

theorem unitUniform_ball_ae_eq_closedBall {m n : ℕ}
    {μ : Measure (Euclidean n)} (hμ : IsUnitUniform m μ)
    {x : Euclidean n} (hx : x ∈ μ.support) {r : ℝ} (hr : 0 < r) :
    ball x r =ᵐ[μ] closedBall x r :=
  ball_ae_eq_closedBall_of_continuous_profile μ x (fun s => s ^ m) hr
    (continuous_pow m).continuousAt (hμ.2.2 x hx)

end Preiss
