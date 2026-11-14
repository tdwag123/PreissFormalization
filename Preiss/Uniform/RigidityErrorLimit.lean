import Preiss.Uniform.RigidityError
import Preiss.Uniform.GaussianLinearGrowth
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped Topology
namespace Preiss
variable {n m : ℕ}
theorem continuous_rigidityError (V : Plane m n) (b : V.1ᗮ)
    (ω : RigidityOmega V) (A : RigidityAdjustedForm V) :
    Continuous (rigidityError V b ω A) := by
  have hP := V.1.orthogonalProjectionOnto.continuous
  have hA := (A.continuous.comp hP).clm_apply hP
  have hω := V.1ᗮ.subtypeL.continuous.comp ((ω.continuous.comp hP).clm_apply hP)
  have hp : Continuous (proj V) := V.1.subtypeL.continuous.comp hP
  exact hA.add (hω.inner ((continuous_id.sub hp).sub continuous_const))

theorem gaussian_rigidityError_limit_of_linear_growth
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (V : Plane m n) (b : V.1ᗮ) (ω : RigidityOmega V) (A : RigidityAdjustedForm V)
    (hlinear : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ μ.support,
      |rigidityError V b ω A z| ≤ C*(1+‖z‖)) :
    Tendsto (fun s : ℝ => (s/gaussianMass μ s)*
      ∫ z, Real.exp (-s*‖z‖^2)*rigidityError V b ω A z ∂μ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := hlinear
  apply normalized_gaussian_integral_tendsto_zero_of_linear_growth μ hm hμ
    (rigidityError V b ω A) (continuous_rigidityError V b ω A).measurable C hC
  letI : μ.Regular := hμ.1
  filter_upwards [μ.support_mem_ae] with z hz
  exact hbound z hz
end Preiss
