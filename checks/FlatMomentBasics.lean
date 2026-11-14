import Preiss.Uniform.FlatMeasure
import Preiss.Uniform.MomentEstimates
import Preiss.Geometry.Projections
import Preiss.Tangent.FlatScaling
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic

open MeasureTheory Metric Set
open scoped ENNReal BigOperators
namespace Preiss
variable {m n : ℕ}

theorem isConical_unitFlat (V : Plane m n) : IsConical m (unitFlat V) := by
  intro r hr
  rw [unitFlat, dimensionalBlowup_smul _ _ _ hr,
    dimensionalBlowup_flatOn V 1 0 V.1.zero_mem r hr]

theorem unitFlat_eq_dirac_of_dim_zero (V : Plane 0 n) :
    unitFlat V = Measure.dirac (0 : Euclidean n) := by
  have hV : V.1 = ⊥ := Submodule.finrank_eq_zero.mp V.property
  have hae : ∀ᵐ z ∂unitFlat V, z = 0 := by
    filter_upwards [(unitFlat V).support_mem_ae] with z hz
    simpa only [unitFlat_support, hV, SetLike.mem_coe, Submodule.mem_bot] using hz
  have hrepr : unitFlat V = unitFlat V {0} • Measure.dirac (0 : Euclidean n) := by
    simpa only [Finset.sum_singleton] using
      (Measure.ae_mem_finset_iff (s := {0} : Finset (Euclidean n))).mp
        (by simpa only [Finset.mem_singleton] using hae)
  have hb := unitFlat_closedBall V 0 V.1.zero_mem zero_lt_one
  rw [hrepr] at hb
  have hmass : unitFlat V {0} = 1 := by simpa using hb
  rw [hrepr, hmass, one_smul]

theorem gaussianMomentForm_dirac_zero_diagonal (k : ℕ) (s : ℝ) (x : Euclidean n) :
    gaussianMomentForm (Measure.dirac (0 : Euclidean n)) k s (fun _ => x) =
      if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [gaussianMomentForm, gaussianMass, momentKernel_apply]
  | succ k => simp [gaussianMomentForm, gaussianMass, momentKernel_apply]

theorem flat_gaussianMoment_diagonal_dim_zero (V : Plane 0 n) (j : ℕ)
    (s : ℝ) (x : Euclidean n) :
    gaussianMomentForm (unitFlat V) (2*j) s (fun _ => x) =
      s ^ j * ‖proj V x‖ ^ (2*j) / (j.factorial : ℝ) := by
  have hV : V.1 = ⊥ := Submodule.finrank_eq_zero.mp V.property
  have hproj : proj V x = 0 := by
    have h := (V.1.orthogonalProjectionOnto x).property
    simpa only [hV, Submodule.mem_bot] using h
  rw [unitFlat_eq_dirac_of_dim_zero, gaussianMomentForm_dirac_zero_diagonal, hproj]
  cases j <;> simp

theorem gaussianMomentForm_unitFlat_diagonal_project (V : Plane m n) (k : ℕ)
    (s : ℝ) (hs : 0 < s) (x : Euclidean n) :
    gaussianMomentForm (unitFlat V) k s (fun _ => x) =
      gaussianMomentForm (unitFlat V) k s (fun _ => proj V x) := by
  have hg := IsUnitUniform.hasPolynomialGrowthBound (unitFlat V) (isUnitUniform_unitFlat V)
  have hint := integrable_gaussianMomentKernel_of_integrable_norm (unitFlat V) k s
    (integrable_norm_pow_mul_gaussian_of_ball_bound (unitFlat V) 1 (m : ℝ)
      hg.1 hg.2.2 k s hs)
  rw [gaussianMomentForm_apply _ _ _ hint, gaussianMomentForm_apply _ _ _ hint]
  unfold gaussianMoment
  congr 1
  apply integral_congr_ae
  filter_upwards [(unitFlat V).support_mem_ae] with z hz
  rw [unitFlat_support] at hz
  have hinner : inner ℝ z (proj V x) = inner ℝ z x := by
    have h := V.1.starProjection_inner_eq_zero x z hz
    rw [inner_sub_left, real_inner_comm x z,
      real_inner_comm (V.1.starProjection x) z] at h
    change inner ℝ z x - inner ℝ z (proj V x) = 0 at h
    linarith
  simp only [hinner]

end Preiss
#print axioms Preiss.isConical_unitFlat
#print axioms Preiss.unitFlat_eq_dirac_of_dim_zero
#print axioms Preiss.gaussianMomentForm_dirac_zero_diagonal
#print axioms Preiss.flat_gaussianMoment_diagonal_dim_zero
#print axioms Preiss.gaussianMomentForm_unitFlat_diagonal_project
