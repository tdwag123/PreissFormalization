module
public import Preiss.Analysis.BilinearTrace
public import Preiss.Analysis.GaussianMoments
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_integral_bilinear_eq_trace (A : E →L[ℝ] E →L[ℝ] ℝ) :
    (∫ v, A v v ∂stdGaussian E) = bilinearTrace A := by
  classical
  let e := stdOrthonormalBasis ℝ E
  let T := InnerProductSpace.continuousLinearMapOfBilin A
  have hLp : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hcov (u v : E) :
      (∫ z, inner ℝ u z * inner ℝ v z ∂stdGaussian E) = inner ℝ u v := by
    calc
      _ = covarianceBilin (stdGaussian E) u v := by
        simpa only [id_eq, integral_id_stdGaussian, sub_zero] using
          (covarianceBilin_apply hLp u v).symm
      _ = inner ℝ u v := by rw [covarianceBilin_stdGaussian]; rfl
  have hdecomp (x : E) :
      A x x = ∑ i, inner ℝ (e i) x * inner ℝ (T (e i)) x := by
    calc
      A x x = A (∑ i, e.repr x i • e i) x := by rw [e.sum_repr]
      _ = ∑ i, e.repr x i * A (e i) x := by simp
      _ = _ := by
        dsimp [T]
        simp only [OrthonormalBasis.repr_apply_apply,
          InnerProductSpace.continuousLinearMapOfBilin_apply]
  simp_rw [hdecomp]
  rw [integral_finsetSum]
  · rw [bilinearTrace_eq_sum_diagonal A e]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcov]
    dsimp [T]
    rw [real_inner_comm, InnerProductSpace.continuousLinearMapOfBilin_apply]
  · intro i _
    exact (hLp.const_inner (e i)).integrable_mul (hLp.const_inner (T (e i)))

theorem gaussian_integral_bilinear_sq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ u v, A u v = A v u) :
    (∫ v, (A v v) ^ 2 ∂stdGaussian E) =
      (bilinearTrace A) ^ 2 + 2 * ∑ i, ∑ j, (A (e i) (e j)) ^ 2 := by
  classical
  let T := InnerProductSpace.continuousLinearMapOfBilin A
  have hT (u v : E) : inner ℝ (T u) v = A u v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply A u v
  have hdecomp (v : E) : A v v = ∑ i, inner ℝ (e i) v * inner ℝ (T (e i)) v := by
    calc
      _ = A (∑ i, e.repr v i • e i) v := by rw [e.sum_repr]
      _ = ∑ i, e.repr v i * A (e i) v := by simp
      _ = _ := by simp only [OrthonormalBasis.repr_apply_apply, hT]
  have hsq (v : E) : (A v v)^2 = ∑ i, ∑ j,
      inner ℝ (e i) v * inner ℝ (T (e i)) v * inner ℝ (e j) v * inner ℝ (T (e j)) v := by
    rw [hdecomp, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfirst : (∑ i, ∑ j, inner ℝ (e i) (T (e i)) * inner ℝ (e j) (T (e j))) =
      (bilinearTrace A)^2 := by
    simp_rw [real_inner_comm (T _) (e _), hT]
    rw [bilinearTrace_eq_sum_diagonal A e, pow_two, Finset.sum_mul_sum]
  have hsecond : (∑ i, ∑ j, inner ℝ (e i) (e j) * inner ℝ (T (e i)) (T (e j))) =
      ∑ i, ∑ j, (A (e i) (e j))^2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [orthonormal_iff_ite.mp e.orthonormal, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, real_inner_self_eq_norm_sq, ← e.sum_sq_inner_left (T (e i))]
    simp only [Finset.mem_univ, if_true, hT]
  have hthird : (∑ i, ∑ j, inner ℝ (e i) (T (e j)) * inner ℝ (T (e i)) (e j)) =
      ∑ i, ∑ j, (A (e i) (e j))^2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (T (e j)) (e i), hT, hT, hA (e j) (e i), pow_two]
  simp_rw [hsq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_gaussian_four_inner (e i) (T (e i)) (e j) (T (e j))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_gaussian_four_inner _ _ _ _),
    gaussian_integral_four_inner, Finset.sum_add_distrib]
  rw [hfirst, hsecond, hthird]
  ring

theorem gaussian_integral_bilinear_sq_ge_trace_sq
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ u v, A u v = A v u)
    (hdim : 0 < Module.finrank ℝ E) :
    (1 + 2 / (Module.finrank ℝ E : ℝ)) * (bilinearTrace A) ^ 2 ≤
      ∫ v, (A v v) ^ 2 ∂stdGaussian E := by
  classical
  let e := stdOrthonormalBasis ℝ E
  let S : ℝ := ∑ i, ∑ j, (A (e i) (e j)) ^ 2
  have hd : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
  have hdiag : (∑ i, (A (e i) (e i)) ^ 2) ≤ S := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => sq_nonneg (A (e i) (e j))) (Finset.mem_univ i)
  have htrace : (bilinearTrace A) ^ 2 ≤
      (Module.finrank ℝ E : ℝ) * ∑ i, (A (e i) (e i)) ^ 2 := by
    rw [bilinearTrace_eq_sum_diagonal A e]
    simpa using sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun i => A (e i) (e i))
  have htraceS : (bilinearTrace A) ^ 2 ≤ (Module.finrank ℝ E : ℝ) * S :=
    htrace.trans (mul_le_mul_of_nonneg_left hdiag hd.le)
  calc
    (1 + 2 / (Module.finrank ℝ E : ℝ)) * (bilinearTrace A) ^ 2 =
        (bilinearTrace A) ^ 2 + 2 * (bilinearTrace A) ^ 2 /
          (Module.finrank ℝ E : ℝ) := by ring
    _ ≤ (bilinearTrace A) ^ 2 + 2 * S := by
      apply add_le_add le_rfl
      apply (div_le_iff₀ hd).mpr
      nlinarith
    _ = ∫ v, (A v v) ^ 2 ∂stdGaussian E :=
      (gaussian_integral_bilinear_sq e A hA).symm


theorem integrable_gaussian_bilinear_diagonal
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] E →L[ℝ] F) :
    Integrable (fun v => A v v) (stdGaussian E) := by
  classical
  let e := stdOrthonormalBasis ℝ E
  have hdecomp (v : E) : A v v = ∑ i, ∑ j,
      (inner ℝ (e i) v * inner ℝ (e j) v) • A (e i) (e j) := by
    conv_lhs => rw [← e.sum_repr v]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul, OrthonormalBasis.repr_apply_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  simp_rw [hdecomp]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hLp : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  exact ((hLp.const_inner (e i)).integrable_mul (hLp.const_inner (e j))).smul_const _

theorem integrable_gaussian_inner_sq_smul_bilinear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] E →L[ℝ] F) (y : E) :
    Integrable (fun v => (inner ℝ y v)^2 • A v v) (stdGaussian E) := by
  classical
  let e := stdOrthonormalBasis ℝ E
  have hdecomp (v : E) : A v v = ∑ i, ∑ j,
      (inner ℝ (e i) v * inner ℝ (e j) v) • A (e i) (e j) := by
    conv_lhs => rw [← e.sum_repr v]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul, OrthonormalBasis.repr_apply_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  simp_rw [hdecomp, Finset.smul_sum, smul_smul, pow_two, ← mul_assoc]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (integrable_gaussian_four_inner y y (e i) (e j)).smul_const _

theorem gaussian_integral_inner_sq_mul_bilinear
    (A : E →L[ℝ] E →L[ℝ] ℝ) (y : E) :
    (∫ v, (inner ℝ y v) ^ 2 * A v v ∂stdGaussian E) =
      ‖y‖ ^ 2 * bilinearTrace A + 2 * A y y := by
  classical
  let e := stdOrthonormalBasis ℝ E
  let T := InnerProductSpace.continuousLinearMapOfBilin A
  have hT (u v : E) : inner ℝ (T u) v = A u v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply A u v
  have hdecomp (v : E) : A v v = ∑ i, inner ℝ (e i) v * inner ℝ (T (e i)) v := by
    calc
      _ = A (∑ i, e.repr v i • e i) v := by rw [e.sum_repr]
      _ = ∑ i, e.repr v i * A (e i) v := by simp
      _ = _ := by simp only [OrthonormalBasis.repr_apply_apply, hT]
  have hprod (v : E) : (inner ℝ y v)^2 * A v v =
      ∑ i, inner ℝ y v * inner ℝ y v * inner ℝ (e i) v * inner ℝ (T (e i)) v := by
    rw [hdecomp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htrace : (∑ i, inner ℝ (e i) (T (e i))) = bilinearTrace A := by
    rw [bilinearTrace_eq_sum_diagonal A e]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (T (e i)) (e i), hT]
  have hcontract : (∑ i, inner ℝ y (e i) * inner ℝ y (T (e i))) = A y y := by
    calc
      _ = ∑ i, e.repr y i * A (e i) y := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (T (e i)) y, hT, OrthonormalBasis.repr_apply_apply,
          real_inner_comm (e i) y]
      _ = A (∑ i, e.repr y i • e i) y := by simp
      _ = A y y := by rw [e.sum_repr]
  simp_rw [hprod]
  rw [integral_finsetSum _ (fun i _ => integrable_gaussian_four_inner y y (e i) (T (e i)))]
  simp_rw [gaussian_integral_four_inner, Finset.sum_add_distrib, real_inner_self_eq_norm_sq]
  rw [← Finset.mul_sum, htrace, hcontract]
  have hreverse : (∑ i, inner ℝ y (T (e i)) * inner ℝ y (e i)) = A y y := by
    simpa only [mul_comm] using hcontract
  rw [hreverse]
  ring


end Preiss
