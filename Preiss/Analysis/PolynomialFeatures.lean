module
public import Preiss.Geometry.Euclidean
public import Preiss.Analysis.Grading
public import Preiss.Analysis.OrthonormalProjection
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
open scoped BigOperators
namespace Preiss

abbrev PolynomialFeatureIndex (n N : ℕ) := Σ k : Fin N, (Fin (k.val + 1) → Fin n)
abbrev PolynomialFeatureSpace (n N : ℕ) := EuclideanSpace ℝ (PolynomialFeatureIndex n N)

noncomputable def polynomialFeature {n : ℕ} (N : ℕ) (x : Euclidean n) :
    PolynomialFeatureSpace n N :=
  WithLp.toLp 2 (fun i =>
    Real.sqrt ((2 : ℝ) ^ (i.1.val + 1) / ((i.1.val + 1).factorial : ℝ)) *
      ∏ j, x (i.2 j))

noncomputable def polynomialFeatureBlock {n N : ℕ} (k : Fin N) :
    Submodule ℝ (PolynomialFeatureSpace n N) :=
  Submodule.span ℝ (Set.range (fun ι : Fin (k.val + 1) → Fin n =>
    EuclideanSpace.single (⟨k, ι⟩ : PolynomialFeatureIndex n N) (1 : ℝ)))

noncomputable def polynomialFeatureProjection {n N : ℕ} (k : Fin N) :
    PolynomialFeatureSpace n N →L[ℝ] PolynomialFeatureSpace n N :=
  (polynomialFeatureBlock (n := n) k).starProjection

theorem polynomialFeatureProjection_apply {n N : ℕ} (k : Fin N)
    (x : PolynomialFeatureSpace n N) (i : PolynomialFeatureIndex n N) :
    polynomialFeatureProjection k x i = if i.1 = k then x i else 0 := by
  classical
  let u : (Fin (k.val+1) → Fin n) → PolynomialFeatureSpace n N :=
    fun j => EuclideanSpace.single ⟨k,j⟩ 1
  have hu : Orthonormal ℝ u := by
    simpa only [u, Function.comp_def, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (PolynomialFeatureIndex n N) ℝ).orthonormal.comp
        (fun j : Fin (k.val+1) → Fin n => (⟨k,j⟩ : PolynomialFeatureIndex n N))
        (fun a b h => by simpa using h)
  change (Submodule.span ℝ (Set.range u)).starProjection x i = _
  rw [starProjection_span_orthonormal_apply u hu]
  obtain ⟨l,j⟩ := i
  by_cases hl : l = k
  · subst l
    simp [u, EuclideanSpace.inner_single_left, Pi.single_apply]
  · have hne (a : Fin (k.val+1) → Fin n) :
        (⟨k,a⟩ : PolynomialFeatureIndex n N) ≠ ⟨l,j⟩ := by
      intro h
      exact hl (congrArg Sigma.fst h).symm
    simp [u, hl, EuclideanSpace.inner_single_left, PiLp.single_apply, hne]

theorem polynomialFeature_inner {n N : ℕ} (x y : Euclidean n) :
    inner ℝ (polynomialFeature N x) (polynomialFeature N y) =
      ∑ k : Fin N, ((2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)) *
        (inner ℝ x y) ^ (k.val + 1) := by
  classical
  change (∑ i : PolynomialFeatureIndex n N,
      (Real.sqrt ((2 : ℝ) ^ (i.1.val + 1) / ((i.1.val + 1).factorial : ℝ)) *
        ∏ j, y (i.2 j)) *
      (Real.sqrt ((2 : ℝ) ^ (i.1.val + 1) / ((i.1.val + 1).factorial : ℝ)) *
        ∏ j, x (i.2 j))) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [show inner ℝ x y = ∑ i : Fin n, y i * x i from rfl,
    Fintype.sum_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ι _
  rw [Finset.prod_mul_distrib]
  let c : ℝ := (2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  change (Real.sqrt c * ∏ j, y (ι j)) * (Real.sqrt c * ∏ j, x (ι j)) =
    c * ((∏ j, y (ι j)) * ∏ j, x (ι j))
  calc
    _ = (Real.sqrt c * Real.sqrt c) * ((∏ j, y (ι j)) * ∏ j, x (ι j)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hc]

theorem polynomialFeatureProjection_isOrthogonalGrading (n N : ℕ) :
    IsOrthogonalGrading (polynomialFeatureProjection (n := n) (N := N)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i x y
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  · intro i
    ext x j
    by_cases hji : j.1 = i <;>
      simp [ContinuousLinearMap.comp_apply, polynomialFeatureProjection_apply, hji]
  · intro i j hij
    ext x k
    by_cases hki : k.1 = i
    · simp [ContinuousLinearMap.comp_apply, polynomialFeatureProjection_apply, hki, hij]
    · simp [ContinuousLinearMap.comp_apply, polynomialFeatureProjection_apply, hki]
  · ext x i
    simp [ContinuousLinearMap.sum_apply, polynomialFeatureProjection_apply]

theorem polynomialFeatureProjection_inner {n N : ℕ} (k : Fin N)
    (x y : Euclidean n) :
    inner ℝ (polynomialFeatureProjection k (polynomialFeature N x))
      (polynomialFeature N y) =
      ((2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)) *
        (inner ℝ x y) ^ (k.val + 1) := by
  classical
  change (∑ i : PolynomialFeatureIndex n N,
    polynomialFeature N y i * polynomialFeatureProjection k (polynomialFeature N x) i) = _
  simp_rw [polynomialFeatureProjection_apply]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · simp only [if_pos rfl]
    change (∑ j : Fin (k.val + 1) → Fin n,
      (Real.sqrt ((2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)) * ∏ a, y (j a)) *
      (Real.sqrt ((2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)) * ∏ a, x (j a))) = _
    rw [show inner ℝ x y = ∑ i : Fin n, y i * x i from rfl,
      Fintype.sum_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.prod_mul_distrib]
    let c : ℝ := (2 : ℝ) ^ (k.val + 1) / ((k.val + 1).factorial : ℝ)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    change (Real.sqrt c * ∏ a, y (j a)) * (Real.sqrt c * ∏ a, x (j a)) =
      c * ((∏ a, y (j a)) * ∏ a, x (j a))
    calc
      _ = (Real.sqrt c * Real.sqrt c) * ((∏ a, y (j a)) * ∏ a, x (j a)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hc]
  · intro l hl hlk
    simp [hlk]
  · simp

theorem norm_pow_eq_sum_coordinate_monomials {n : ℕ} (x : Euclidean n) (d : ℕ) :
    ‖x‖ ^ (2 * d) = ∑ f : Fin d → Fin n, (∏ j, x (f j)) ^ 2 := by
  have hn : ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change (∑ i : Fin n, x i * x i) = _
    simp only [pow_two]
  rw [pow_mul, hn, Fintype.sum_pow]
  simp only [Finset.prod_pow]

theorem exists_normPolynomial_feature_functionals (n q : ℕ) :
    ∃ L : Fin q → PolynomialFeatureSpace n (2 * q) →L[ℝ] ℝ,
      ∀ j x, L j (polynomialFeature (2 * q) x) = ‖x‖ ^ (2 * (j.val + 1)) := by
  classical
  suffices ∀ j : Fin q, ∃ L : PolynomialFeatureSpace n (2 * q) →L[ℝ] ℝ,
      ∀ x, L (polynomialFeature (2 * q) x) = ‖x‖ ^ (2 * (j.val+1)) by
    choose L hL using this
    exact ⟨L,hL⟩
  intro j
  let d := j.val + 1
  let k : Fin (2*q) := ⟨d+d-1, by dsimp [d]; omega⟩
  have hkd : k.val+1 = d+d := by dsimp [k,d]; omega
  let e : Fin (k.val+1) ≃ Fin (d+d) := finCongr hkd
  let ζ : (Fin d → Fin n) → Fin (k.val+1) → Fin n :=
    fun f => (Fin.append f f) ∘ e
  let c : ℝ := Real.sqrt ((2 : ℝ)^(k.val+1) / ((k.val+1).factorial : ℝ))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c⁻¹ • ∑ f : Fin d → Fin n,
    EuclideanSpace.proj (⟨k,ζ f⟩ : PolynomialFeatureIndex n (2*q)), ?_⟩
  intro x
  have hprod (f : Fin d → Fin n) :
      (∏ a, x (ζ f a)) = (∏ a, x (f a))^2 := by
    calc
      _ = ∏ a : Fin (d+d), x (Fin.append f f a) :=
        Fintype.prod_equiv e _ _ (fun a => rfl)
      _ = _ := by
        rw [Fin.prod_univ_add]
        simp only [Fin.append_left, Fin.append_right, pow_two]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    EuclideanSpace.coe_proj, smul_eq_mul]
  change c⁻¹ * (∑ f : Fin d → Fin n, c * ∏ a, x (ζ f a)) = _
  rw [← Finset.mul_sum]
  simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, hprod]
  exact (norm_pow_eq_sum_coordinate_monomials x d).symm

theorem polynomialFeature_weighted_inner {n N : ℕ} (s : ℝ) (x z : Euclidean n) :
    inner ℝ (polynomialFeature N z)
      (weightedGrading polynomialFeatureProjection s (polynomialFeature N x)) =
      ∑ k : Fin N, (s ^ (k.val+1) *
        ((2 : ℝ) ^ (k.val+1) / ((k.val+1).factorial : ℝ))) *
          (inner ℝ z x) ^ (k.val+1) := by
  simp only [weightedGrading, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_comm (polynomialFeatureProjection k (polynomialFeature N x))
      (polynomialFeature N z), polynomialFeatureProjection_inner,
    real_inner_comm z x]
  ring

end Preiss
