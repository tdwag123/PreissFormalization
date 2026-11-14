module
public import Preiss.Uniform.MomentFeatures
public import Preiss.Analysis.AnalyticJets
public import Preiss.Analysis.AsymptoticCoefficients

/-! # Finite Taylor jets of Gaussian moments in the symmetric-form subspace -/

@[expose] public section
namespace Preiss
open MeasureTheory Filter Set Asymptotics
open scoped BigOperators Topology
variable {n m : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem exists_gaussianMoment_finite_jets
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (d q : ℕ) (hq : 0 < q) :
    ∃ A : ℕ → SymmetricMomentForm n (d+1), ∀ j : ℕ, 0 < j → j ≤ q →
      IsLittleO (𝓝[>] (0 : ℝ))
        (fun s => symmetricGaussianMomentForm μ (d+1) s -
          ∑ i ∈ Finset.range j,s^(i+1) • A (i+1))
        (fun s : ℝ => s^j) := by
  let Q := d+q+1
  have hQ : 0 < Q := by dsimp [Q]; omega
  let k : Fin (2*Q) := ⟨d,by dsimp [Q]; omega⟩
  let R : (PolynomialFeatureSpace n (2*Q) →L[ℝ] ℝ) →L[ℝ]
      SymmetricMomentForm n (d+1) := symmetricPolynomialFeatureMomentRecovery (n := n) k
  obtain ⟨a,ha,ha0,herror⟩ := exists_featureMoment_analytic_approximation μ hm hμ Q hQ
  have hRa : AnalyticAt ℝ (fun s => R (a s)) 0 :=
    (ContinuousLinearMap.analyticAt (𝕜 := ℝ)
      (E := PolynomialFeatureSpace n (2*Q) →L[ℝ] ℝ)
      (F := SymmetricMomentForm n (d+1)) R _).comp ha
  have hRa0 : R (a 0) = 0 := by rw [ha0,map_zero]
  obtain ⟨A,hA⟩ := exists_positive_taylor_jets_of_analyticAt_zero _ hRa hRa0
  have hrecover (s : ℝ) (hs : 0 < s) :
      R (featureMoment μ (2*Q) s) = symmetricGaussianMomentForm μ (d+1) s := by
    apply Subtype.ext
    exact polynomialFeatureMomentRecovery_featureMoment_of_growth μ 1 (m : ℝ)
      (IsUnitUniform.hasPolynomialGrowthBound μ hμ) k s hs
  have hRerror : IsBigO (𝓝[>] (0 : ℝ))
      (fun s => symmetricGaussianMomentForm μ (d+1) s - R (a s))
      (fun s : ℝ => s^((Q : ℝ)+1/2)) := by
    have h := (ContinuousLinearMap.isBigO_comp (𝕜₂ := ℝ) (𝕜₃ := ℝ)
      (F := PolynomialFeatureSpace n (2*Q) →L[ℝ] ℝ)
      (G := SymmetricMomentForm n (d+1)) R
      (fun s => featureMoment μ (2*Q) s - a s) (𝓝[>] (0 : ℝ))).trans herror
    apply h.congr' _ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [map_sub,hrecover s hs]
  refine ⟨A,?_⟩
  intro j hj hjq
  have hremainder : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => symmetricGaussianMomentForm μ (d+1) s - R (a s))
      (fun s : ℝ => s^j) := by
    apply hRerror.trans_isLittleO
    simpa only [Real.rpow_natCast] using
      (isLittleO_rpow_nhdsGT_zero (a := (Q : ℝ)+1/2) (b := (j : ℝ)) (by
        have hnat : j ≤ Q := by dsimp [Q]; omega
        have hreal : (j : ℝ) ≤ (Q : ℝ) := Nat.cast_le.mpr hnat
        linarith))
  have hjet := (hA j).mono (l := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
  convert hremainder.add hjet using 1 <;> first | rfl | (funext s; abel)

end Preiss
