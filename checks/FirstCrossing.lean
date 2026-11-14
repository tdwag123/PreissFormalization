import Preiss.Theorem.FirstCrossing
import Preiss.Uniform.ConicalGap
import Preiss.Uniform.TangentAtInfinity
import Preiss.Tangent.Continuity
import Preiss.Tangent.Algebra
import Preiss.Tangent.FlatScaling
import Preiss.Geometry.PlaneRegularity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

open MeasureTheory Metric Set Filter
open scoped Topology CompactlySupported
namespace Preiss
variable {n m : ℕ}

theorem vague_limit_unique
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) (ν ξ : Measure X)
    (hν : ν.Regular) (hξ : ξ.Regular)
    (hμν : Measure.WeaklyConverges μ ν) (hμξ : Measure.WeaklyConverges μ ξ) : ν = ξ := by
  letI : ν.Regular := hν
  letI : ξ.Regular := hξ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact tendsto_nhds_unique (hμν f) (hμξ f)

theorem exists_flatnessGap_checked (hm : 0 < m) (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ) :
    ∃ ε : ℝ, IsFlatnessGap m φ ε := by
  obtain ⟨ε, hε, hflat⟩ := conical_flatness_gap hm hmn
  refine ⟨ε, hε, ?_⟩
  intro ν hν hc hf
  exact hflat ν hν hc (exists_plane_ball_energy_le_of_flatness_le hmn φ hφ ν hν.1 ε hf)

theorem first_crossing_ratio_tendsto_atTop_checked (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (x : Euclidean n)
    (α ξ : Measure (Euclidean n)) (hα : IsFlat m α) (hξ : IsUnitUniform m ξ)
    (r σ : ℕ → ℝ) (hcross : FirstCrossingData m μ x φ ε α ξ r σ) :
    Tendsto (fun i => r i / σ i) atTop atTop := by
  classical
  obtain ⟨hσ, hr0, hrα, hσξ, hξflat, hσflat, hinterval⟩ := hcross
  have hratio1 (i : ℕ) : 1 ≤ r i / σ i :=
    (le_div_iff₀ (hσ i).1).mpr (by simpa only [one_mul] using (hσ i).2)
  have hratioPos (i : ℕ) : 0 < r i / σ i := lt_of_lt_of_le zero_lt_one (hratio1 i)
  apply tendsto_atTop.mpr
  intro M
  by_contra hnot
  have hfreq : ∃ᶠ i in atTop, r i / σ i ∈ Icc 1 M := by
    apply (not_eventually.mp hnot).mono
    intro i hi
    exact ⟨hratio1 i, (lt_of_not_ge hi).le⟩
  obtain ⟨s, hs, τ, hτ, hlim⟩ := isCompact_Icc.tendsto_subseq' hfreq
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs.1
  have hconv := vague_dimensionalBlowup_moving (m := m)
    (fun i => dimensionalBlowup m μ x (σ (τ i))) ξ
    (fun i => regular_dimensionalBlowup μ hμ x (hσ (τ i)).1) hξ.1
    (fun f => (hσξ f).comp hτ.tendsto_atTop) (fun _ => 0) 0 tendsto_const_nhds
    (fun i => r (τ i) / σ (τ i)) s (fun i => hratioPos (τ i)) hspos hlim
  have hcomp (i : ℕ) :
      dimensionalBlowup m (dimensionalBlowup m μ x (σ (τ i))) 0
        (r (τ i) / σ (τ i)) = dimensionalBlowup m μ x (r (τ i)) := by
    rw [dimensionalBlowup_comp _ _ _ _ _ (hσ (τ i)).1 (hratioPos (τ i)), smul_zero, add_zero]
    congr 1
    field_simp [(hσ (τ i)).1.ne']
  simp_rw [hcomp] at hconv
  have hαreg : α.Regular := by
    obtain ⟨V, c, hc, hctop, rfl⟩ := hα
    exact regular_flatOn V hctop.ne
  have heq : dimensionalBlowup m ξ 0 s = α :=
    vague_limit_unique _ _ _ (regular_dimensionalBlowup ξ hξ.1 0 hspos) hαreg hconv
      (fun f => (hrα f).comp hτ.tendsto_atTop)
  have hflat : IsFlat m ξ := isFlat_of_dimensionalBlowup_zero ξ s hspos (by rw [heq]; exact hα)
  have hz := flatness_eq_zero_of_isFlat φ hφ ξ hflat
  exact hε.ne' (hz.symm.trans hξflat).symm

theorem first_crossing_limit_flat_at_infinity_checked (hm : 0 < m) (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (ε : ℝ) (hε : IsFlatnessGap m φ ε)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (x : Euclidean n)
    (α ξ : Measure (Euclidean n)) (hξ : IsUnitUniform m ξ)
    (r σ : ℕ → ℝ) (hcross : FirstCrossingData m μ x φ ε α ξ r σ)
    (hratio : Tendsto (fun i => r i / σ i) atTop atTop) :
    (∀ R ≥ 1, flatness m φ (dimensionalBlowup m ξ 0 R) ≤ ε) ∧
    ∀ ψ, IsTangentAtInfinity m ξ ψ → IsFlat m ψ := by
  obtain ⟨hσ, hr0, hrα, hσξ, hξflat, hσflat, hinterval⟩ := hcross
  have hscale (R : ℝ) (hR : 1 ≤ R) : flatness m φ (dimensionalBlowup m ξ 0 R) ≤ ε := by
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hconv := vague_dimensionalBlowup_moving (m := m)
      (fun i => dimensionalBlowup m μ x (σ i)) ξ
      (fun i => regular_dimensionalBlowup μ hμ x (hσ i).1) hξ.1 hσξ
      (fun _ => 0) 0 tendsto_const_nhds (fun _ => R) R
      (fun _ => hRpos) hRpos tendsto_const_nhds
    have hcomp (i : ℕ) : dimensionalBlowup m (dimensionalBlowup m μ x (σ i)) 0 R =
        dimensionalBlowup m μ x (σ i * R) := by
      simpa only [smul_zero, add_zero] using
        dimensionalBlowup_comp μ x 0 (σ i) R (hσ i).1 hRpos
    have ht := flatness_continuous hmn φ hφ _ _
      (fun i => regular_dimensionalBlowup _
        (regular_dimensionalBlowup μ hμ x (hσ i).1) 0 hRpos)
      (regular_dimensionalBlowup ξ hξ.1 0 hRpos) hconv
    apply le_of_tendsto ht
    filter_upwards [hratio.eventually (eventually_ge_atTop R)] with i hi
    rw [hcomp]
    apply hinterval i (σ i * R)
    refine ⟨?_, ?_⟩
    · nlinarith [(hσ i).1]
    · have hh := (le_div_iff₀ (hσ i).1).mp hi
      simpa only [mul_comm] using hh
  refine ⟨hscale, ?_⟩
  intro ψ hψ
  have huψ := isUnitUniform_of_tangentAtInfinity ξ ψ hξ hψ
  apply hε.2 ψ huψ (tangent_at_infinity_conical hm hmn ξ ψ hξ hψ)
  obtain ⟨hψreg, hψne, R, hRpos, hRtop, hlim⟩ := hψ
  have ht := flatness_continuous hmn φ hφ _ _
    (fun i => regular_dimensionalBlowup ξ hξ.1 0 (hRpos i)) hψreg hlim
  apply le_of_tendsto ht
  filter_upwards [hRtop.eventually (eventually_ge_atTop 1)] with i hi
  exact hscale (R i) hi

end Preiss

#print axioms Preiss.vague_limit_unique
#print axioms Preiss.exists_flatnessGap_checked
#print axioms Preiss.first_crossing_ratio_tendsto_atTop_checked
#print axioms Preiss.first_crossing_limit_flat_at_infinity_checked
