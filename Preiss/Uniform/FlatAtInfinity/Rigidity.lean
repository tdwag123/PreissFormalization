import Preiss.Uniform.TraceRigidity
import Preiss.Uniform.MomentTrace
import Preiss.Uniform.Classification
import Preiss.Uniform.TangentAtInfinity
import Mathlib.Tactic

/-! # Rigidity of a uniform measure with a flat tangent at infinity -/
open MeasureTheory
namespace Preiss
variable {n m : ℕ}

theorem flat_of_flat_at_infinity (μ ν : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (hInfinity : IsTangentAtInfinity m μ ν) (hν : IsFlat m ν) : IsFlat m μ := by
  have hνuniform := isUnitUniform_of_tangentAtInfinity μ ν hμ hInfinity
  obtain ⟨V,c,hc,hct,hrepr⟩ := hν
  have hsupp : ν.support = (V.1 : Set (Euclidean n)) := by
    rw [hrepr]
    exact flatOn_support V hc
  have hνeq := unitUniform_eq_flat_of_support_subset_plane hm ν hνuniform V hsupp.subset
  have hV : IsTangentAtInfinity m μ (unitFlat V) := by simpa only [hνeq] using hInfinity
  obtain ⟨B,hB⟩ := exists_gaussianMoment_taylor_coefficients μ hm hμ
  obtain ⟨b,hb⟩ := exists_firstMomentNormalVector μ hm hμ B hB V hV
  have htrace := trace_secondMomentCoefficient_eq_zero μ hm hμ B hB
  obtain ⟨ω,hω,A,hA⟩ := exists_rigidityOmega_and_adjustedForm μ hm hμ B hB V hV b hb
  have hbound := secondMomentCoefficient_trace_lower_bound μ hm hμ B hB V hV b hb ω hω A hA
  rw [htrace] at hbound
  have hd : 0 < (m:ℝ)+2 := by positivity
  have hbzero : b = 0 := by
    have h := (div_le_iff₀ hd).mp hbound
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg b, sq_nonneg ‖b‖]
  have hμsupp : μ.support ⊆ (V.1 : Set (Euclidean n)) := by
    intro x hx
    have h := (support_normal_sq_eq_inner μ hm hμ B hB V hV b hb x hx).2.2
    rw [hbzero, norm_zero, mul_zero] at h
    have heq : x = proj V x := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    rw [heq]
    exact (V.1.orthogonalProjectionOnto x).property
  rw [unitUniform_eq_flat_of_support_subset_plane hm μ hμ V hμsupp]
  exact isFlat_unitFlat V
end Preiss
