import Preiss.Analysis.LeadingHomogeneousTerm
import Preiss.Analysis.MultilinearDiagonal
import Preiss.Analysis.Vague.Support
import Preiss.Uniform.MomentExpansion
import Preiss.Uniform.BoundedTube
import Preiss.Geometry.UnitFlat
import Preiss.Uniform.MomentVague
import Preiss.Uniform.BlowdownMoments
import Preiss.Uniform.FlatMoments
import Preiss.Uniform.FlatMeasure
import Preiss.Uniform.Scaling
import Preiss.Uniform.MomentCoefficients
import Preiss.Uniform.Defs
import Preiss.Tangent.Defs
import Preiss.Geometry.Projections
import Preiss.Geometry.PlaneMeasure
import Preiss.Analysis.BilinearTrace
import Preiss.Geometry.NormalCoordinates
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace Preiss
variable {n m : ℕ}

/-- An explicit normal vector representing the first Taylor coefficient. -/
def IsFirstMomentNormalVector (B : MomentCoefficientFamily n) (V : Plane m n)
    (b : V.1ᗮ) : Prop :=
  ∀ x : Euclidean n, B 1 1 (fun _ => x) = 2 * inner ℝ (b : Euclidean n) x

/-- The first coefficient has a normal Riesz representative whenever its restriction
to the plane vanishes. This lemma does not assume a moment expansion or a blow-down. -/
theorem exists_firstMomentNormalVector_of_restrict_eq_zero
    (B : MomentCoefficientFamily n) (V : Plane m n)
    (hzero : ∀ u : V.1, B 1 1 (fun _ => (u : Euclidean n)) = 0) :
    ∃ b : V.1ᗮ, IsFirstMomentNormalVector B V b := by
  let A : Euclidean n →L[ℝ] ℝ :=
    continuousMultilinearCurryFin1 ℝ (Euclidean n) ℝ (B 1 1)
  have hA (x : Euclidean n) : A x = B 1 1 (fun _ => x) := by
    dsimp only [A]
    rw [continuousMultilinearCurryFin1_apply]
    congr 1
  let L : Euclidean n →L[ℝ] ℝ := (1 / 2 : ℝ) • A
  have hL : ∀ x ∈ V.1, L x = 0 := by
    intro x hx
    have hz := hzero ⟨x, hx⟩
    simp only [L, ContinuousLinearMap.smul_apply, smul_eq_mul, hA, hz, mul_zero]
  obtain ⟨b, hb⟩ := exists_orthogonal_representative V.1 L hL
  refine ⟨b, ?_⟩
  intro x
  have h := hb x
  simp only [L, ContinuousLinearMap.smul_apply, smul_eq_mul, hA] at h
  linarith

theorem evenMomentCoefficient_eq_projection_norm
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (j : ℕ) (hj : 0 < j) (x : Euclidean n) :
    B (2 * j) j (fun _ => x) = ‖proj V x‖ ^ (2 * j) := by
  obtain ⟨hreg, _, r, hr, hrinf, hlim⟩ := hV
  have hν (i : ℕ) := isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i)
  have hmoment := (blowdown_gaussianMoment_even_limit μ hm hμ B hB j hj).comp hrinf
  have heval := ((ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin (2*j) => Euclidean n) ℝ (fun _ => x)).continuous.tendsto
      ((j.factorial : ℝ)⁻¹ • B (2*j) j)).comp hmoment
  have hvague := vague_gaussianMomentForm_apply hm _ (unitFlat V) hν
    (isUnitUniform_unitFlat V) hlim (2*j) 1 zero_lt_one (fun _ => x)
  have heq := tendsto_nhds_unique heval hvague
  simp only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    flat_gaussianMoment_diagonal V j 1 zero_lt_one x, one_pow, one_mul] at heq
  have hf : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  apply mul_left_cancel₀ (inv_ne_zero hf)
  simpa only [div_eq_mul_inv, mul_comm] using heq

theorem oddMomentCoefficient_restrict_plane_eq_zero
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (j : ℕ) (hj : 0 < j) (u : Fin (2 * j - 1) → V.1) :
    B (2 * j - 1) j (fun i => (u i : Euclidean n)) = 0 := by
  classical
  let d := 2*j-1
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdsucc : d+1 = 2*j := by dsimp [d]; omega
  let A : (k : ℕ) → MomentForm n k := fun k => if k = 0 then 0 else B k j
  have hpoly (z : Euclidean n) (hz : z ∈ μ.support) :
      0 ≤ ∑ k ∈ Finset.range (d+1), A k (fun _ => z) := by
    have hsum := sum_gaussianMomentCoefficient_eq_norm_pow μ hm hμ B hB j hj z hz
    have heven := evenMomentCoefficient_eq_projection_norm μ hm hμ B hB V hV j hj z
    have hproj : ‖proj V z‖ ≤ ‖z‖ := V.1.norm_orthogonalProjectionOnto_apply_le z
    have hpow := pow_le_pow_left₀ (norm_nonneg (proj V z)) hproj (2*j)
    rw [← hdsucc, Finset.sum_range_succ] at hsum
    rw [hdsucc, heven] at hsum
    have hshift : (∑ k ∈ Finset.range (d+1), A k (fun _ => z)) =
        ∑ k ∈ Finset.range d, B (k+1) j (fun _ => z) := by
      rw [Finset.sum_range_succ']
      simp [A]
    rw [hshift]
    linarith
  have hnonneg (v : V.1) : 0 ≤ B d j (fun _ => (v : Euclidean n)) := by
    obtain ⟨hreg, _, r, hr, hrinf, hlim⟩ := hV
    have hν (i : ℕ) := isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i)
    have hv : (v : Euclidean n) ∈ (unitFlat V).support := by
      rw [unitFlat_support]
      exact v.property
    obtain ⟨y, hmem, hy⟩ := exists_support_sequence_of_vague _ _
      (fun i => (hν i).1) hreg hlim v hv
    have hrescale : ∀ᶠ i in atTop, r i • y i ∈ μ.support := by
      filter_upwards [hmem] with i hi
      rw [dimensionalBlowup_support μ 0 (hr i)] at hi
      obtain ⟨z, hz, hzy⟩ := hi
      rw [← hzy]
      simpa only [sub_zero, smul_smul, mul_inv_cancel₀ (hr i).ne', one_smul] using hz
    have h := leading_diagonal_nonneg_of_rescaled_points A d μ.support hpoly
      r hr hrinf y v hy hrescale
    simpa only [A, if_neg hdpos.ne'] using h
  have hdiag (v : V.1) : B d j (fun _ => (v : Euclidean n)) = 0 := by
    have hpos := hnonneg v
    have hneg := hnonneg (-v)
    have hdodd : Odd d := ⟨j-1, by dsimp [d]; omega⟩
    have hmap := (B d j).map_smul_univ (fun _ : Fin d => (-1 : ℝ))
      (fun _ => (v : Euclidean n))
    have heq : B d j (fun _ => (-(v : Euclidean n))) =
        - B d j (fun _ => (v : Euclidean n)) := by
      simpa only [neg_one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        hdodd.neg_one_pow, neg_one_smul] using hmap
    change 0 ≤ B d j (fun _ => (-(v : Euclidean n))) at hneg
    rw [heq] at hneg
    linarith
  let T := (B d j).compContinuousLinearMap (fun _ => V.1.subtypeL)
  have hT : T = 0 := symmetricMultilinear_eq_zero_of_diagonal T
    (fun σ v => hB.1 d j σ (fun i => (v i : Euclidean n))) hdiag
  exact congrArg (fun f : ContinuousMultilinearMap ℝ (fun _ : Fin d => V.1) ℝ => f u) hT


theorem exists_firstMomentNormalVector
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V)) :
    ∃ b : V.1ᗮ, IsFirstMomentNormalVector B V b := by
  apply exists_firstMomentNormalVector_of_restrict_eq_zero B V
  intro u
  simpa using oddMomentCoefficient_restrict_plane_eq_zero μ hm hμ B hB V hV
    1 zero_lt_one (fun _ => u)

theorem support_normal_sq_eq_inner
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b)
    (x : Euclidean n) (hx : x ∈ μ.support) :
    ‖x - proj V x‖ ^ 2 = 2 * inner ℝ (b : Euclidean n) x ∧
    ‖x - proj V x - (b : Euclidean n)‖ = ‖b‖ ∧
    ‖x - proj V x‖ ≤ 2 * ‖b‖ := by
  have hs := sum_gaussianMomentCoefficient_eq_norm_pow μ hm hμ B hB 1 zero_lt_one x hx
  have he : B 2 1 (fun _ => x) = ‖proj V x‖ ^ 2 := by
    simpa using evenMomentCoefficient_eq_projection_norm μ hm hμ B hB V hV 1 zero_lt_one x
  norm_num [Finset.sum_range_succ] at hs
  rw [he, hb x] at hs
  exact normal_coordinates_of_quadratic_identity V.1 b x hs


theorem exists_uniform_dist_plane_support_bound
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V)) :
    ∃ R : ℝ, 0 < R ∧ ∀ v : V.1, infDist (v : Euclidean n) μ.support < R := by
  obtain ⟨b, hb⟩ := exists_firstMomentNormalVector μ hm hμ B hB V hV
  apply exists_plane_to_support_bound_of_bounded_normal_coordinates hm μ hμ V
    (show 0 ≤ 2 * ‖b‖ by positivity)
  intro x hx
  exact (support_normal_sq_eq_inner μ hm hμ B hB V hV b hb x hx).2.2

theorem trace_secondMomentCoefficient_normal_eq
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b) :
    bilinearTrace (restrictBilinear (momentBilinear (B 2 2)) V.1ᗮ) = 8 * ‖b‖ ^ 2 := by
  sorry

end Preiss
