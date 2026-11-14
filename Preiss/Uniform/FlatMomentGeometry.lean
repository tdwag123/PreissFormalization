module
public import Preiss.Uniform.FlatMeasure
public import Preiss.Uniform.MomentEstimates
public import Preiss.Geometry.Projections
public import Preiss.Tangent.FlatScaling
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Tactic

@[expose] public section
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
      (Measure.ae_mem_finset_iff (s := ({0} : Finset (Euclidean n)))).mp
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
    change ((V.1.orthogonalProjectionOnto x : V.1) : Euclidean n) = 0
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
    rw [inner_sub_left] at h
    have heq : inner ℝ x z = inner ℝ (proj V x) z := sub_eq_zero.mp h
    calc
      _ = inner ℝ (proj V x) z := real_inner_comm _ _
      _ = inner ℝ x z := heq.symm
      _ = _ := real_inner_comm _ _
  simp only [hinner]

theorem gaussianMomentForm_unitFlat_zero_diagonal (V : Plane m n)
    (s : ℝ) (hs : 0 < s) (x : Euclidean n) :
    gaussianMomentForm (unitFlat V) 0 s (fun _ => x) = 1 := by
  have hg := IsUnitUniform.hasPolynomialGrowthBound (unitFlat V) (isUnitUniform_unitFlat V)
  have hint := integrable_gaussianMomentKernel_of_integrable_norm (unitFlat V) 0 s
    (integrable_norm_pow_mul_gaussian_of_ball_bound (unitFlat V) 1 (m : ℝ)
      hg.1 hg.2.2 0 s hs)
  have hmass := integral_gaussian_pos_of_ball_bound (unitFlat V) (unitFlat_ne_zero V)
    1 (m : ℝ) hg.1 hg.2.2 s hs
  rw [gaussianMomentForm_apply _ _ _ hint]
  simpa only [gaussianMoment, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    one_mul, Finset.univ_eq_empty, Finset.prod_empty] using inv_mul_cancel₀ hmass.ne'

end Preiss
