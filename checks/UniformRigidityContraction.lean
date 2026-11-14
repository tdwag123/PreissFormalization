import Preiss.Analysis.BilinearIntegralLimits
import Preiss.Analysis.GaussianBilinearNorm
import Preiss.Uniform.RigidityError
import Preiss.Analysis.WeightedIntegralPolarization
import Preiss.Uniform.FlatAtInfinity.TraceLimits
import Preiss.Uniform.MomentCoefficientLimits
import Mathlib.Tactic

open MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators
namespace Preiss
variable {m n : ℕ}

theorem gaussian_bilinear_contraction_of_weighted_moment_limits
    {X I E F ι κ : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ F)
    (μ : Measure X) (l : Filter I) [l.NeBot]
    (weight : I → X → ℝ) (scale : I → ℝ) (p : X → E) (q : X → F)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (ω : E →L[ℝ] E →L[ℝ] F)
    (hsymm : ∀ u v, ω u v = ω v u)
    (hmean : (∫ v, ω v v ∂stdGaussian E) = 0)
    (hint₂ : ∀ i j, ∀ᶠ t in l,
      Integrable (fun x => weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x))) μ)
    (hlim₂ : ∀ i j, Tendsto (fun t => scale t * ∫ x,
      weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x)) ∂μ)
      l (𝓝 (inner ℝ (e i) (e j) / 2)))
    (hint₃ : ∀ i j, ∀ᶠ t in l,
      Integrable (fun x => weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x) *
        inner ℝ (ω (e i) (e j)) (q x))) μ)
    (hlim₃ : ∀ i j, Tendsto (fun t => scale t * ∫ x,
      weight t x * (inner ℝ (e i) (p x) * inner ℝ (e j) (p x) *
        inner ℝ (ω (e i) (e j)) (q x)) ∂μ) l (𝓝 (‖ω (e i) (e j)‖^2 / 8)))
    (hzero : Tendsto (fun t => scale t * ∫ x, weight t x *
      (A (p x) (p x) + inner ℝ (ω (p x) (p x)) (q x)) ∂μ) l (𝓝 0)) :
    (∫ v, ‖ω v v‖^2 ∂stdGaussian E) = -8 * ∫ v, A v v ∂stdGaussian E := by
  classical
  let Q (ij : ι × ι) (x : X) := inner ℝ (e ij.1) (p x) * inner ℝ (e ij.2) (p x)
  let a (ij : ι × ι) := A (e ij.1) (e ij.2)
  let L (ij : ι × ι) := inner ℝ (e ij.1) (e ij.2) / 2
  have hquad := tendsto_weighted_integral_finite_linear_combination μ l weight scale Q a L
    (fun ij => hint₂ ij.1 ij.2) (fun ij => hlim₂ ij.1 ij.2)
  have hQ (x : X) : (∑ ij : ι × ι, a ij * Q ij x) = A (p x) (p x) := by
    dsimp only [a, Q]
    rw [Fintype.sum_prod_type, bilinear_diagonal_eq_sum_orthonormalBasis e A (p x)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_eq_mul]
    ring
  simp_rw [hQ] at hquad
  have hL : (∑ ij : ι × ι, a ij * L ij) = bilinearTrace A / 2 := by
    rw [bilinearTrace_eq_sum_diagonal A e]
    simp [a, L, Fintype.sum_prod_type, e.inner_eq_ite, Finset.sum_div, ite_div, mul_ite]
  rw [hL] at hquad
  let T (ij : ι × ι) (x : X) := Q ij x * inner ℝ (ω (e ij.1) (e ij.2)) (q x)
  let N (ij : ι × ι) := ‖ω (e ij.1) (e ij.2)‖^2 / 8
  have hmixed := tendsto_weighted_integral_finite_linear_combination μ l weight scale T
    (fun _ => 1) N (fun ij => hint₃ ij.1 ij.2) (fun ij => hlim₃ ij.1 ij.2)
  have hT (x : X) : (∑ ij : ι × ι, (1 : ℝ) * T ij x) =
      inner ℝ (ω (p x) (p x)) (q x) := by
    dsimp only [T, Q]
    rw [Fintype.sum_prod_type, bilinear_diagonal_eq_sum_orthonormalBasis e ω (p x)]
    simp only [one_mul, sum_inner, real_inner_smul_left]
  simp_rw [hT] at hmixed
  have hN : (∑ ij : ι × ι, (1 : ℝ) * N ij) =
      (∑ i, ∑ j, ‖ω (e i) (e j)‖^2) / 8 := by
    simp only [N, one_mul, Fintype.sum_prod_type, Finset.sum_div]
  rw [hN] at hmixed
  have htotal : Tendsto (fun t => scale t * ∫ x, weight t x *
      (A (p x) (p x) + inner ℝ (ω (p x) (p x)) (q x)) ∂μ)
      l (𝓝 (bilinearTrace A / 2 + (∑ i, ∑ j, ‖ω (e i) (e j)‖^2) / 8)) := by
    apply (hquad.2.add hmixed.2).congr'
    filter_upwards [hquad.1, hmixed.1] with t htA htω
    have hsum : (fun x => weight t x * (A (p x) (p x) + inner ℝ (ω (p x) (p x)) (q x))) =
        (fun x => weight t x * A (p x) (p x) + weight t x * inner ℝ (ω (p x) (p x)) (q x)) := by
      funext x
      ring
    rw [hsum, integral_add htA htω]
    ring
  have heq := tendsto_nhds_unique hzero htotal
  rw [gaussian_integral_norm_sq_bilinear_of_mean_zero e f ω hsymm hmean,
    gaussian_integral_bilinear_eq_trace]
  nlinarith


theorem integrable_gaussian_inner_sq_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (s : ℝ) (hs : 0 < s) (u : Euclidean n) :
    Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2) μ := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euclidean n) ℝ
    ![u,u]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 2 s hs)
  simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
    Fin.prod_univ_two, pow_two, mul_assoc] using h

theorem integrable_gaussian_inner_sq_centered_unitUniform
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (s : ℝ) (hs : 0 < s) (b u w : Euclidean n) :
    Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 * inner ℝ (z-b) w) μ := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Euclidean n) ℝ
    ![u,u,w]).integrable_comp (integrable_gaussianMomentKernel μ hm hμ 3 s hs)
  have h₃ : Integrable (fun z => Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 * inner ℝ z w) μ := by
    simpa [Function.comp_def, ContinuousMultilinearMap.smul_apply, momentKernel_apply,
      Fin.prod_univ_three, pow_two, mul_assoc] using h
  have h₂ := integrable_gaussian_inner_sq_unitUniform μ hm hμ s hs u
  simpa only [Pi.sub_apply, inner_sub_left, mul_sub] using h₃.sub (h₂.mul_const (inner ℝ b w))

theorem normalized_gaussian_inner_sq_limit
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B) (u : Euclidean n) :
    Tendsto (fun s => (s / gaussianMass μ s) *
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (B 2 1 ![u,u] / 2)) := by
  have ht := (gaussianMoment_first_scaled_limit μ B hB 2 (by decide) ![u,u]).div_const 2
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  rw [gaussianMomentForm_apply μ 2 s (integrable_gaussianMomentKernel μ hm hμ 2 s hs')]
  simp only [gaussianMoment, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  have hi : (∫ z, (inner ℝ z u * inner ℝ z u) * Real.exp (-s*‖z‖^2) ∂μ) =
      ∫ z, Real.exp (-s*‖z‖^2) * (inner ℝ z u)^2 ∂μ := by
    congr 1
    funext z
    ring
  rw [hi]
  norm_num
  have hmass : gaussianMass μ s ≠ 0 := by
    rw [gaussianMass_unitUniform μ hm hμ s hs']
    exact (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hs' _)).ne'
  unfold gaussianMass at hmass ⊢
  simp only [neg_mul] at hmass ⊢
  field_simp [hmass, hs'.ne']
  <;> ring

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
        exact Submodule.starProjection_eq_self.mpr a.property
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
      have hv : proj V (a : Euclidean n) = a := Submodule.starProjection_eq_self.mpr a.property
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
#print axioms Preiss.integrable_gaussian_inner_sq_unitUniform
#print axioms Preiss.integrable_gaussian_inner_sq_centered_unitUniform
#print axioms Preiss.normalized_gaussian_inner_sq_limit
#print axioms Preiss.normalized_gaussian_inner_mul_limit_on_plane
#print axioms Preiss.normalized_gaussian_mixed_limit_rigidityOmega

#print axioms Preiss.gaussian_bilinear_contraction_of_weighted_moment_limits
#print axioms Preiss.rigidityOmega_contraction_of_mean_zero_and_error_limit
