module
public import Preiss.Uniform.MomentExpansion
public import Preiss.Uniform.MomentCovariance
public import Preiss.Uniform.Scaling
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Tactic

@[expose] public section
namespace Preiss
open MeasureTheory Filter Set
open scoped BigOperators Topology
variable {n m : ℕ}

theorem tendsto_inv_sq_atTop_nhdsGT_zero :
    Tendsto (fun r : ℝ => (r^2)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
  have hpow : Tendsto (fun r : ℝ => r^2) atTop atTop := by
    simpa only [Real.rpow_two] using tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_inv_atTop_zero.comp hpow,?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact inv_pos.mpr (sq_pos_of_pos hr)

theorem exists_blowdown_gaussianMoment_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (k : ℕ) (hk : 0 < k) :
    ∃ L : MomentForm n k, Tendsto
      (fun r : ℝ => gaussianMomentForm (dimensionalBlowup m μ 0 r) k 1) atTop (𝓝 L) := by
  obtain ⟨B,hB⟩ := exists_gaussianMoment_taylor_coefficients μ hm hμ
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨j,rfl⟩ := even_iff_exists_two_mul.mp he
    have hj : 0 < j := by omega
    refine ⟨((j.factorial : ℝ)⁻¹) • B (2*j) j,
      ((gaussianMoment_scaled_even_limit μ hm hμ B hB j hj).comp
        tendsto_inv_sq_atTop_nhdsGT_zero).congr' ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [gaussianMomentForm_dilate (m := m) μ (2*j) 1 r hr,one_div]
    simp only [Function.comp_apply,inv_pow,inv_inv,pow_mul]
  · refine ⟨0,((gaussianMoment_scaled_odd_limit μ hm hμ B hB k ho).comp
      tendsto_inv_sq_atTop_nhdsGT_zero).congr' ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [gaussianMomentForm_dilate (m := m) μ k 1 r hr,one_div]
    have hp : ((r^2)⁻¹)^(-(k : ℝ)/2) = r^k := by
      calc
        _ = (r^(-2 : ℝ))^(-(k : ℝ)/2) := by rw [Real.rpow_neg hr.le,Real.rpow_two]
        _ = r^((-2 : ℝ)*(-(k : ℝ)/2)) := (Real.rpow_mul hr.le _ _).symm
        _ = r^(k : ℝ) := by congr 1; ring
        _ = _ := Real.rpow_natCast _ _
    simp only [Function.comp_apply, hp]

theorem gaussian_integral_product_eq_moment
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (k : ℕ) (u : Fin k → Euclidean n) :
    (∫ z, (∏ i,inner ℝ z (u i)) * Real.exp (-‖z‖^2) ∂μ) =
      ((k.factorial : ℝ)/2^k * Real.Gamma ((m : ℝ)/2+1)) *
        gaussianMomentForm μ k 1 u := by
  have hmass : gaussianMass μ 1 = Real.Gamma ((m : ℝ)/2+1) := by
    simpa using gaussianMass_unitUniform μ hm hμ 1 zero_lt_one
  have hform : gaussianMomentForm μ k 1 u =
      ((2 : ℝ)^k/(k.factorial : ℝ) * (Real.Gamma ((m : ℝ)/2+1))⁻¹) *
        ∫ z, (∏ i,inner ℝ z (u i)) * Real.exp (-‖z‖^2) ∂μ := by
    rw [gaussianMomentForm_apply μ k 1 (integrable_gaussianMomentKernel μ hm hμ k 1 zero_lt_one)]
    change (((2 : ℝ)*1)^k/(k.factorial : ℝ) * (gaussianMass μ 1)⁻¹) *
      (∫ z, (∏ i,inner ℝ z (u i)) * Real.exp (-1*‖z‖^2) ∂μ) = _
    rw [hmass]
    simp
  rw [hform]
  have hg : Real.Gamma ((m : ℝ)/2+1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hkfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hg,hkfac]

theorem exists_blowdown_product_gaussian_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (k : ℕ) (u : Fin k → Euclidean n) :
    ∃ l : ℝ, Tendsto (fun r : ℝ => ∫ z,
      (∏ i,inner ℝ z (u i)) * Real.exp (-‖z‖^2)
        ∂dimensionalBlowup m μ 0 r) atTop (𝓝 l) := by
  by_cases hk : k = 0
  · subst k
    refine ⟨Real.Gamma ((m : ℝ)/2+1),tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hν := isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 hr
    symm
    simpa [gaussianMass] using gaussianMass_unitUniform
      (dimensionalBlowup m μ 0 r) hm hν 1 zero_lt_one
  · obtain ⟨L,hL⟩ := exists_blowdown_gaussianMoment_limit μ hm hμ k (Nat.pos_of_ne_zero hk)
    have hEval := ((ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin k => Euclidean n) ℝ u).continuous.tendsto L).comp hL
    refine ⟨((k.factorial : ℝ)/2^k * Real.Gamma ((m : ℝ)/2+1)) * L u,
      (tendsto_const_nhds.mul hEval).congr' ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (gaussian_integral_product_eq_moment (dimensionalBlowup m μ 0 r) hm
      (isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 hr) k u).symm

theorem exists_coordinate_product_representation (d : Fin n →₀ ℕ) :
    ∃ k : ℕ, ∃ u : Fin k → Euclidean n, ∀ z : Euclidean n,
      d.prod (fun j a => z j ^ a) = ∏ i,inner ℝ z (u i) := by
  classical
  let I := Σ j : Fin n, Fin (d j)
  let k := Fintype.card I
  let e : Fin k ≃ I := (Fintype.equivFin I).symm
  let u : Fin k → Euclidean n := fun i => EuclideanSpace.single (e i).1 1
  refine ⟨k,u,?_⟩
  intro z
  rw [d.prod_fintype (fun j a => z j^a) (fun _ => pow_zero _)]
  calc
    (∏ j,z j^(d j)) = ∏ a : I,z a.1 := by
      dsimp [I]
      rw [Fintype.prod_sigma]
      simp
    _ = ∏ i : Fin k,z (e i).1 := (Equiv.prod_comp e (fun a : I => z a.1)).symm
    _ = _ := by simp [u,EuclideanSpace.inner_single_right]

theorem integrable_polynomial_gaussian_unitUniform
    (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ)
    (P : MvPolynomial (Fin n) ℝ) :
    Integrable (fun z => MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖^2)) μ := by
  have hg := IsUnitUniform.hasPolynomialGrowthBound μ hμ
  simpa only [pow_zero,one_mul,neg_one_mul] using
    integrable_norm_pow_mul_polynomial_mul_gaussian μ 1 (m : ℝ) hg.1 hg.2.2 P 0 1 zero_lt_one

theorem blowdown_gaussian_polynomial_limit (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (P : MvPolynomial (Fin n) ℝ) :
    ∃ l : ℝ, Tendsto (fun r : ℝ => ∫ z,
      MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖^2)
        ∂dimensionalBlowup m μ 0 r) atTop (𝓝 l) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    obtain ⟨k,u,hu⟩ := exists_coordinate_product_representation d
    obtain ⟨l,hl⟩ := exists_blowdown_product_gaussian_limit μ hm hμ k u
    refine ⟨c*l,(tendsto_const_nhds.mul hl).congr' (Filter.Eventually.of_forall ?_)⟩
    intro r
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [MvPolynomial.eval_monomial,hu]
    ring
  | add P Q hP hQ =>
    obtain ⟨l,hl⟩ := hP
    obtain ⟨t,ht⟩ := hQ
    refine ⟨l+t,(hl.add ht).congr' ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hν := isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 hr
    rw [← integral_add (integrable_polynomial_gaussian_unitUniform _ hν P)
      (integrable_polynomial_gaussian_unitUniform _ hν Q)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [MvPolynomial.eval_add,add_mul]

end Preiss
