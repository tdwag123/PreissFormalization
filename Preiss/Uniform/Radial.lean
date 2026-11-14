module
public import Preiss.Uniform.Defs
public import Preiss.Geometry.PlaneMeasure
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
open MeasureTheory Metric Set
namespace Preiss
variable {n m : ℕ}

theorem uniform_radial_pushforward (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (y : Euclidean n) (hy : y ∈ μ.support)
    (V : Plane m n) :
    μ.map (fun z => ‖z - y‖) = (unitFlat V).map (fun z => ‖z‖) := by
  sorry

theorem integral_gaussian_mul_homogeneous
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (hcone : IsConical m μ)
    (h : Euclidean n → ℝ) (hh : Measurable h) (hnonneg : ∀ z, 0 ≤ h z)
    (a : ℝ) (ha : 0 < (m : ℝ) + a)
    (hhom : ∀ r > 0, ∀ z, h (r • z) = r ^ a * h z)
    (hint : IntegrableOn h (closedBall 0 1) μ) :
    Integrable (fun z => Real.exp (-‖z‖ ^ 2) * h z) μ ∧
    (∫ z, Real.exp (-‖z‖ ^ 2) * h z ∂μ) =
      Real.Gamma (((m : ℝ) + a) / 2 + 1) * ∫ z in closedBall 0 1, h z ∂μ := by
  sorry

end Preiss
