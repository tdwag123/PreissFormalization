module
public import Preiss.Uniform.MomentExpansion
public import Preiss.Uniform.MomentCovariance
public import Preiss.Uniform.MomentTrace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section
namespace Preiss
open MeasureTheory Filter Set Asymptotics
open scoped BigOperators Topology
variable {n m : ℕ}

theorem gaussianMomentForm_homogeneous_of_isConical (μ : Measure (Euclidean n))
    (hc : IsConical m μ) (k : ℕ) (s : ℝ) (hs : 0 < s) :
    gaussianMomentForm μ k s = s ^ ((k : ℝ) / 2) • gaussianMomentForm μ k 1 := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h := gaussianMomentForm_dilate (m := m) μ k s (Real.sqrt s) hr
  rw [hc _ hr,Real.sq_sqrt hs.le,div_self hs.ne'] at h
  have hpow : (Real.sqrt s)^k = s^((k : ℝ)/2) := by
    calc
      _ = (s ^ (1/2 : ℝ)) ^ (k : ℝ) := by rw [Real.sqrt_eq_rpow,Real.rpow_natCast]
      _ = s ^ ((1/2 : ℝ)*(k : ℝ)) := (Real.rpow_mul hs.le _ _).symm
      _ = _ := by congr 1; ring
  simpa only [hpow] using h

theorem conical_gaussianMoment_homogeneous (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    gaussianMomentForm μ k s = s ^ ((k : ℝ) / 2) • gaussianMomentForm μ k 1 :=
  gaussianMomentForm_homogeneous_of_isConical μ hc k s hs

theorem conical_gaussianMoment_odd (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (k : ℕ) (hk : Odd k) (s : ℝ) (hs : 0 < s) : gaussianMomentForm μ k s = 0 := by
  obtain ⟨B,hB⟩ := exists_gaussianMoment_taylor_coefficients μ hm hμ
  have ht := gaussianMoment_scaled_odd_limit μ hm hμ B hB k hk
  have heq : (fun t : ℝ => (t^(-(k : ℝ)/2)) • gaussianMomentForm μ k t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => gaussianMomentForm μ k 1) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [gaussianMomentForm_homogeneous_of_isConical μ hc k t ht,smul_smul,
      show -(k : ℝ)/2 = -((k : ℝ)/2) by ring,Real.rpow_neg ht.le,
      inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht _)),one_smul]
  have hz : gaussianMomentForm μ k 1 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (ht.congr' heq)
  rw [gaussianMomentForm_homogeneous_of_isConical μ hc k s hs,hz,smul_zero]

theorem conical_covariance_eq_norm_sq_on_support (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ)
    (x : Euclidean n) (hx : x ∈ μ.support) :
    gaussianMomentForm μ 2 1 (fun _ => x) = ‖x‖^2 := by
  obtain ⟨B,hB⟩ := exists_gaussianMoment_taylor_coefficients μ hm hμ
  have hb1 : B 1 1 = 0 := by
    have h := (hB.2 1 (by decide) 1 (by decide)).neg_left
    apply eq_zero_of_isLittleO_pow_smul 1
    apply h.congr' _ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [conical_gaussianMoment_odd μ hm hμ hc 1 odd_one s hs]
    simp [momentTaylorPolynomial]
  have hb2 : B 2 1 = gaussianMomentForm μ 2 1 := by
    have h := gaussianMoment_scaled_even_limit μ hm hμ B hB 1 (by decide)
    have heq : (fun s : ℝ => (s^1)⁻¹ • gaussianMomentForm μ 2 s) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun _ => gaussianMomentForm μ 2 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [gaussianMomentForm_homogeneous_of_isConical μ hc 2 s hs]
      norm_num [smul_smul,ne_of_gt (show 0 < s from hs)]
    have ht : Tendsto (fun s : ℝ => (s^1)⁻¹ • gaussianMomentForm μ 2 s)
        (𝓝[>] 0) (𝓝 (B 2 1)) := by simpa using h
    exact tendsto_nhds_unique (ht.congr' heq) tendsto_const_nhds
  simpa [Finset.sum_range_succ,hb1,hb2] using
    sum_gaussianMomentCoefficient_eq_norm_pow μ hm hμ B hB 1 (by decide) x hx

theorem conical_covariance_trace_support (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (hc : IsConical m μ) :
    (∀ x : Euclidean n, 0 ≤ gaussianMomentForm μ 2 1 (fun _ => x)) ∧
    bilinearTrace (momentBilinear (gaussianMomentForm μ 2 1)) = (m : ℝ) ∧
    ∀ x ∈ μ.support, gaussianMomentForm μ 2 1 (fun _ => x) = ‖x‖ ^ 2 := by
  refine ⟨fun x => gaussianMomentForm_even_nonneg μ 2 (by decide) 1 x, ?_,
    fun x hx => conical_covariance_eq_norm_sq_on_support μ hm hμ hc x hx⟩
  simpa using trace_gaussianMomentForm_two μ hm hμ 1 zero_lt_one


end Preiss
