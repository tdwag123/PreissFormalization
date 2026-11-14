module
public import Preiss.Geometry.Euclidean
public import Preiss.Analysis.Grading
public import Preiss.Analysis.MultilinearSymmetrization
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

noncomputable def polynomialFeatureMultilinearBlock {n N : ℕ} (k : Fin N) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k.val+1) => Euclidean n)
      (PolynomialFeatureSpace n N) :=
  ∑ ι : Fin (k.val+1) → Fin n,
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin (k.val+1)) ℝ).compContinuousLinearMap
      (fun j => EuclideanSpace.proj (ι j))).smulRight
        (EuclideanSpace.single (⟨k,ι⟩ : PolynomialFeatureIndex n N)
          (Real.sqrt ((2 : ℝ)^(k.val+1)/((k.val+1).factorial : ℝ))))

theorem polynomialFeatureMultilinearBlock_apply {n N : ℕ} (k : Fin N)
    (u : Fin (k.val+1) → Euclidean n) :
    polynomialFeatureMultilinearBlock k u =
      ∑ ι : Fin (k.val+1) → Fin n, (∏ j, u j (ι j)) •
        EuclideanSpace.single (⟨k,ι⟩ : PolynomialFeatureIndex n N)
          (Real.sqrt ((2 : ℝ)^(k.val+1)/((k.val+1).factorial : ℝ))) := by
  simp [polynomialFeatureMultilinearBlock]

theorem inner_polynomialFeature_multilinearBlock {n N : ℕ} (k : Fin N)
    (z : Euclidean n) (u : Fin (k.val+1) → Euclidean n) :
    inner ℝ (polynomialFeature N z) (polynomialFeatureMultilinearBlock k u) =
      ((2 : ℝ)^(k.val+1)/((k.val+1).factorial : ℝ)) * ∏ j, inner ℝ z (u j) := by
  classical
  let c : ℝ := (2 : ℝ)^(k.val+1)/((k.val+1).factorial : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hexp : (∏ j, inner ℝ z (u j)) =
      ∑ ι : Fin (k.val+1) → Fin n, ∏ j, u j (ι j) * z (ι j) := by
    change (∏ j, ∑ a : Fin n, u j a * z a) = _
    exact Fintype.prod_sum _
  rw [polynomialFeatureMultilinearBlock_apply, inner_sum, hexp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ι _
  simp only [inner_smul_right, EuclideanSpace.inner_single_right, RCLike.conj_to_real]
  change (∏ j, u j (ι j)) * (Real.sqrt c * (Real.sqrt c * ∏ j, z (ι j))) =
    c * ∏ j, u j (ι j) * z (ι j)
  rw [Finset.prod_mul_distrib]
  calc
    _ = (Real.sqrt c * Real.sqrt c) * ((∏ j, u j (ι j)) * ∏ j, z (ι j)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hc]

theorem polynomialFeatureMultilinearBlock_mem {n N : ℕ} (k : Fin N)
    (u : Fin (k.val+1) → Euclidean n) :
    polynomialFeatureMultilinearBlock k u ∈ polynomialFeatureBlock (n := n) k := by
  classical
  rw [polynomialFeatureMultilinearBlock_apply]
  apply Submodule.sum_mem
  intro ι _
  apply Submodule.smul_mem
  have hb : EuclideanSpace.single (⟨k,ι⟩ : PolynomialFeatureIndex n N) (1 : ℝ) ∈
      polynomialFeatureBlock (n := n) k := Submodule.subset_span ⟨ι,rfl⟩
  have hs := (polynomialFeatureBlock (n := n) k).smul_mem
    (Real.sqrt ((2 : ℝ)^(k.val+1)/((k.val+1).factorial : ℝ))) hb
  convert hs using 1
  ext a
  simp [PiLp.single_apply]

theorem weightedGrading_polynomialFeatureMultilinearBlock {n N : ℕ} (k : Fin N)
    (s : ℝ) (u : Fin (k.val+1) → Euclidean n) :
    weightedGrading polynomialFeatureProjection s (polynomialFeatureMultilinearBlock k u) =
      s ^ (k.val+1) • polynomialFeatureMultilinearBlock k u := by
  classical
  have hD := polynomialFeatureProjection_isOrthogonalGrading n N
  have hk : polynomialFeatureProjection k (polynomialFeatureMultilinearBlock k u) =
      polynomialFeatureMultilinearBlock k u :=
    Submodule.starProjection_eq_self_iff.mpr (polynomialFeatureMultilinearBlock_mem k u)
  simp only [weightedGrading,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
  rw [Finset.sum_eq_single k]
  · rw [hk]
  · intro j _ hj
    have hz := congrArg (fun T : PolynomialFeatureSpace n N →L[ℝ] PolynomialFeatureSpace n N =>
      T (polynomialFeatureMultilinearBlock k u)) (hD.2.2.1 j k hj)
    change polynomialFeatureProjection j
      (polynomialFeatureProjection k (polynomialFeatureMultilinearBlock k u)) = 0 at hz
    rw [hk] at hz
    rw [hz,smul_zero]
  · simp

noncomputable def symmetricPolynomialFeatureMultilinearBlock {n N : ℕ} (k : Fin N) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k.val+1) => Euclidean n)
      (PolynomialFeatureSpace n N) :=
  symmetrizeContinuousMultilinearMap (polynomialFeatureMultilinearBlock k)

noncomputable def polynomialFeatureMomentRecovery {n N : ℕ} (k : Fin N) :
    (PolynomialFeatureSpace n N →L[ℝ] ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (k.val+1) => Euclidean n) ℝ :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin (k.val+1) => Euclidean n) (PolynomialFeatureSpace n N) ℝ).flip
      (symmetricPolynomialFeatureMultilinearBlock k)

theorem polynomialFeatureMomentRecovery_symmetric {n N : ℕ} (k : Fin N)
    (f : PolynomialFeatureSpace n N →L[ℝ] ℝ)
    (σ : Equiv.Perm (Fin (k.val+1))) (u : Fin (k.val+1) → Euclidean n) :
    polynomialFeatureMomentRecovery k f (u ∘ σ) = polynomialFeatureMomentRecovery k f u := by
  change f (symmetrizeContinuousMultilinearMap _ (u ∘ σ)) =
    f (symmetrizeContinuousMultilinearMap _ u)
  rw [symmetrizeContinuousMultilinearMap_apply_perm]

noncomputable def symmetricPolynomialFeatureMomentRecovery {n N : ℕ} (k : Fin N) :
    (PolynomialFeatureSpace n N →L[ℝ] ℝ) →L[ℝ]
      symmetricContinuousMultilinearSubmodule
        (ι := Fin (k.val+1)) (E := Euclidean n) (F := ℝ) :=
  (polynomialFeatureMomentRecovery k).codRestrict _
    (fun f => polynomialFeatureMomentRecovery_symmetric k f)

end Preiss
