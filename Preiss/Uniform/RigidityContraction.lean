import Preiss.Analysis.GaussianBilinearContraction
import Preiss.Analysis.WeightedIntegralPolarization
import Preiss.Uniform.GaussianInnerProducts
import Preiss.Uniform.FlatAtInfinity.TraceLimits
import Preiss.Uniform.RigidityError
import Mathlib.Tactic

/-! # The mean-square rigidity contraction from proved moment limits -/
open MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem normalized_gaussian_inner_mul_limit_on_plane
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V)) (u v : V.1) :
    Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * inner ℝ z (u : Euclidean n) * inner ℝ z (v : Euclidean n) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ u v / 2)) := by
  have hdiag (a : V.1) : Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z (a : Euclidean n))^2 ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖a‖^2 / 2)) := by
    have he : B 2 1 ![(a : Euclidean n),(a : Euclidean n)] = ‖a‖^2 := by
      have hvect : ![(a : Euclidean n),(a : Euclidean n)] = (fun _ : Fin 2 => (a : Euclidean n)) := by
        ext i
        fin_cases i <;> rfl
      rw [hvect]
      have he := evenMomentCoefficient_eq_projection_norm μ hm hμ B hB V hV 1 zero_lt_one a
      have hv : proj V (a : Euclidean n) = a := by
        exact Submodule.starProjection_eq_self_iff.mpr a.property
      simpa only [show 2*1=2 by rfl, hv, Submodule.norm_coe] using he
    simpa only [he] using normalized_gaussian_inner_sq_limit μ hm hμ B hB a
  have hints : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z (u : Euclidean n)+inner ℝ z (v : Euclidean n))^2 * 1) μ ∧
      Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z (u : Euclidean n))^2 * 1) μ ∧
      Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z (v : Euclidean n))^2 * 1) μ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨by simpa only [Submodule.coe_add, inner_add_right, mul_one] using
      integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs (u+v),
      by simpa only [mul_one] using integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs u,
      by simpa only [mul_one] using integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs v⟩
  have hsum := hdiag (u+v)
  simp only [Submodule.coe_add, inner_add_right] at hsum
  have ht := tendsto_weighted_integral_mul_of_square_limits μ (𝓝[>] (0 : ℝ))
    (fun s z => Real.exp (-s*‖z‖^2)) (fun s => s/gaussianMass μ s)
    (fun z => inner ℝ z (u : Euclidean n)) (fun z => inner ℝ z (v : Euclidean n)) (fun _ => 1)
    hints _ _ _ (by simpa only [mul_one] using hsum)
    (by simpa only [mul_one] using hdiag u) (by simpa only [mul_one] using hdiag v)
  have he : (‖u+v‖^2 / 2 - ‖u‖^2 / 2 - ‖v‖^2 / 2) / 2 = inner ℝ u v / 2 := by
    rw [norm_add_sq_real]
    ring
  simpa only [mul_one, he] using ht

theorem normalized_gaussian_mixed_limit_rigidityOmega
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω) (u v : V.1) (w : V.1ᗮ) :
    Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * inner ℝ z (u : Euclidean n) * inner ℝ z (v : Euclidean n) *
        inner ℝ (z-(b : Euclidean n)) (w : Euclidean n) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (ω u v) w / 8)) := by
  let p := V.1.orthogonalProjectionOnto
  let q : Euclidean n → V.1ᗮ := fun z => V.1ᗮ.orthogonalProjectionOnto (z-(b : Euclidean n))
  have hint (a : V.1) (w : V.1ᗮ) : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ (p z) a)^2 * inner ℝ (q z) w) μ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [p, q, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using
      integrable_gaussian_inner_sq_centered_unitUniform μ hm hμ s hs b a w
  have hlim (a : V.1) (w : V.1ᗮ) : Tendsto (fun s => (s/gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ (p z) a)^2 * inner ℝ (q z) w ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (ω a a) w / 8)) := by
    have ht := (mixed_gaussian_limit_eq_omega μ hm hμ B hB V hV b hb a w).div_const 8
    have he : B 2 1 ![(a : Euclidean n),(a : Euclidean n)] = inner ℝ a a := by
      have hvect : ![(a : Euclidean n),(a : Euclidean n)] = (fun _ : Fin 2 => (a : Euclidean n)) := by
        ext i
        fin_cases i <;> rfl
      rw [hvect]
      have hv : proj V (a : Euclidean n) = a := Submodule.starProjection_eq_self_iff.mpr a.property
      simpa only [show 2*1=2 by rfl, hv, Submodule.norm_coe, real_inner_self_eq_norm_sq] using
        evenMomentCoefficient_eq_projection_norm μ hm hμ B hB V hV 1 zero_lt_one a
    have homega := hω.2 a a w
    change inner ℝ (ω a a) w = 3 * B 3 2 ![(a : Euclidean n),(a : Euclidean n),(w : Euclidean n)] -
      4 * inner ℝ a a * inner ℝ (b : Euclidean n) (w : Euclidean n) at homega
    rw [he, ← homega] at ht
    apply ht.congr'
    exact Eventually.of_forall fun s => by
      simp only [p, q, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
      ring
  have ht := tendsto_weighted_bilinear_mixed_of_diagonal_limits μ (𝓝[>] (0 : ℝ))
    (fun s z => Real.exp (-s*‖z‖^2)) (fun s => s/gaussianMass μ s) p q ω hω.1 hint hlim u v w
  simpa only [p, q, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using ht

theorem rigidityOmega_contraction_of_mean_zero_and_error_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (ω : RigidityOmega V) (hω : IsRigidityOmega B V b ω)
    (A : RigidityAdjustedForm V)
    (hmean : (∫ v : V.1, ω v v ∂stdGaussian V.1) = 0)
    (herror : Tendsto (fun s : ℝ => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * rigidityError V b ω A z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ v : V.1, ‖ω v v‖^2 ∂stdGaussian V.1) =
      -8 * ∫ v : V.1, A v v ∂stdGaussian V.1 := by
  classical
  let e := stdOrthonormalBasis ℝ V.1
  let f := stdOrthonormalBasis ℝ V.1ᗮ
  let p := V.1.orthogonalProjectionOnto
  let q : Euclidean n → V.1ᗮ := fun z => V.1ᗮ.orthogonalProjectionOnto (z-(b : Euclidean n))
  have hint₂ (u v : V.1) (s : ℝ) (hs : 0 < s) : Integrable
      (fun z => Real.exp (-s*‖z‖^2) * inner ℝ z (u : Euclidean n) * inner ℝ z (v : Euclidean n)) μ := by
    have h := integrable_weighted_mul_of_squares μ (fun z => Real.exp (-s*‖z‖^2))
      (fun z => inner ℝ z (u : Euclidean n)) (fun z => inner ℝ z (v : Euclidean n)) (fun _ => 1)
      (by simpa only [inner_add_right, mul_one] using
        integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs ((u : Euclidean n)+v))
      (by simpa only [mul_one] using integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs u)
      (by simpa only [mul_one] using integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs v)
    simpa only [mul_one] using h
  have hint₃ (u v : V.1) (w : V.1ᗮ) (s : ℝ) (hs : 0 < s) : Integrable
      (fun z => Real.exp (-s*‖z‖^2) * inner ℝ z (u : Euclidean n) * inner ℝ z (v : Euclidean n) *
        inner ℝ (z-(b : Euclidean n)) (w : Euclidean n)) μ := by
    apply integrable_weighted_mul_of_squares
    · simpa only [inner_add_right] using
        integrable_gaussian_inner_sq_centered_unitUniform μ hm hμ s hs b ((u : Euclidean n)+v) w
    · exact integrable_gaussian_inner_sq_centered_unitUniform μ hm hμ s hs b u w
    · exact integrable_gaussian_inner_sq_centered_unitUniform μ hm hμ s hs b v w
  apply gaussian_bilinear_contraction_of_weighted_moment_limits e f μ (𝓝[>] (0 : ℝ))
    (fun s z => Real.exp (-s*‖z‖^2)) (fun s => s/gaussianMass μ s) p q A ω hω.1 hmean
  · intro i j
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [p, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
      real_inner_comm (e i : Euclidean n), real_inner_comm (e j : Euclidean n), mul_assoc] using
      hint₂ (e i) (e j) s hs
  · intro i j
    simpa only [p, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
      real_inner_comm (e i : Euclidean n), real_inner_comm (e j : Euclidean n), mul_assoc] using
      normalized_gaussian_inner_mul_limit_on_plane μ hm hμ B hB V hV (e i) (e j)
  · intro i j
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [p, q, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
      real_inner_comm (e i : Euclidean n), real_inner_comm (e j : Euclidean n),
      real_inner_comm (ω (e i) (e j) : Euclidean n), mul_assoc] using
      hint₃ (e i) (e j) (ω (e i) (e j)) s hs
  · intro i j
    simpa only [p, q, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
      real_inner_comm (e i : Euclidean n), real_inner_comm (e j : Euclidean n),
      real_inner_comm (ω (e i) (e j) : Euclidean n), mul_assoc,
      real_inner_self_eq_norm_sq] using
      normalized_gaussian_mixed_limit_rigidityOmega μ hm hμ B hB V hV b hb ω hω
        (e i) (e j) (ω (e i) (e j))
  · have heq (z : Euclidean n) :
        A (p z) (p z) + inner ℝ (ω (p z) (p z)) (q z) = rigidityError V b ω A z := by
      dsimp only [q, rigidityError, p]
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
      have hz : inner ℝ (ω (V.1.orthogonalProjectionOnto z) (V.1.orthogonalProjectionOnto z) : Euclidean n)
          (proj V z) = 0 := V.1.inner_left_of_mem_orthogonal
            (V.1.orthogonalProjectionOnto z).property (ω _ _).property
      simp only [inner_sub_right, hz, sub_zero]
    simpa only [heq] using herror

end Preiss
