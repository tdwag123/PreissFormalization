import Preiss.Uniform.FlatAtInfinity.Basic
import Preiss.Uniform.FlatMoments
import Preiss.Uniform.MomentVague
import Preiss.Uniform.BlowdownMoments
import Preiss.Analysis.LeadingHomogeneousTerm
import Preiss.Analysis.MultilinearDiagonal
import Preiss.Uniform.MomentExpansion
import Preiss.Uniform.Scaling
import Preiss.Uniform.FlatMeasure
import Preiss.Analysis.Vague.Support
import Preiss.Geometry.UnitFlat
import Mathlib.Tactic

namespace Preiss
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {n m : ℕ}

theorem evenMomentCoefficient_eq_projection_norm_draft
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

theorem oddMomentCoefficient_restrict_plane_eq_zero_draft
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
    have heven := evenMomentCoefficient_eq_projection_norm_draft μ hm hμ B hB V hV j hj z
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

end Preiss
