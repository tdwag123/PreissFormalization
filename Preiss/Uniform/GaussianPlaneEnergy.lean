module

public import Preiss.Uniform.MomentEstimates
public import Preiss.Geometry.Planes
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Integrability of Gaussian squared distance to a plane -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {n m : ℕ}

theorem integrable_gaussian_planeEnergy_of_unitUniform
    (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ) (V : Plane m n) :
    Integrable (fun z => Real.exp (-‖z‖ ^ 2) * (infDist z (V.1 : Set (Euclidean n))) ^ 2) μ := by
  have hi := integrable_norm_pow_mul_gaussian_of_polynomial_growth μ hμ.1 1 (m : ℝ)
    (IsUnitUniform.hasPolynomialGrowthBound μ hμ) 2 1 zero_lt_one
  have hi' : Integrable (fun z => Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ 2) μ := by
    simpa only [one_mul, neg_mul, mul_comm] using hi
  apply hi'.mono' ((Real.continuous_exp.comp ((continuous_norm.pow 2).neg)).mul
    ((continuous_infDist_pt (V.1 : Set (Euclidean n))).pow 2)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖Real.exp (-‖z‖ ^ 2) * (infDist z (V.1 : Set (Euclidean n))) ^ 2‖ ≤
    Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ infDist_nonneg
  simpa only [dist_zero_right] using (infDist_le_dist_of_mem (x := z) V.1.zero_mem)

end Preiss
