import Preiss.Uniform.Compactness
import Preiss.Uniform.BlowdownMoments
import Preiss.Analysis.GaussianVague
import Preiss.Analysis.GaussianMomentDetermination
import Preiss.Tangent.Defs
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

namespace Preiss
open MeasureTheory Filter Set Metric
open scoped Topology CompactlySupported
variable {n m : ℕ}

theorem IsUnitUniform.ne_zero (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ) :
    μ ≠ 0 := by
  intro h
  simpa only [h, Measure.support_zero, Set.mem_empty_iff_false] using hμ.2.1

theorem isUnitUniform_of_tangentAtInfinity
    (μ ν : Measure (Euclidean n)) (hμ : IsUnitUniform m μ)
    (hν : IsTangentAtInfinity m μ ν) : IsUnitUniform m ν := by
  obtain ⟨hreg, _, r, hr, _, hlim⟩ := hν
  exact isUnitUniform_of_vague _
    (fun i => isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i)) ν hreg hlim

theorem exists_unitUniform_tangentAtInfinity
    (μ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ) :
    ∃ ν, IsUnitUniform m ν ∧ IsTangentAtInfinity m μ ν := by
  let r : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hr (i : ℕ) : 0 < r i := by dsimp [r]; positivity
  have hrinf : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨φ, ν, hφ, hν, hlim⟩ := exists_vague_subsequence_unitUniform
    (fun i => dimensionalBlowup m μ 0 (r i))
    (fun i => isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i))
  exact ⟨ν, hν, hν.1, IsUnitUniform.ne_zero ν hν,
    r ∘ φ, fun i => hr (φ i), hrinf.comp hφ.tendsto_atTop, hlim⟩

theorem tangentAtInfinity_eq_of_unitUniform (hm : 0 < m)
    (μ ν ξ : Measure (Euclidean n)) (hμ : IsUnitUniform m μ)
    (hν : IsTangentAtInfinity m μ ν) (hξ : IsTangentAtInfinity m μ ξ) : ν = ξ := by
  have huν := isUnitUniform_of_tangentAtInfinity μ ν hμ hν
  have huξ := isUnitUniform_of_tangentAtInfinity μ ξ hμ hξ
  apply measure_eq_of_gaussian_polynomial_moments_eq ν ξ huν.1 huξ.1 1 (m : ℝ)
    (IsUnitUniform.hasPolynomialGrowthBound ν huν)
    (IsUnitUniform.hasPolynomialGrowthBound ξ huξ)
  intro P
  obtain ⟨l, hl⟩ := blowdown_gaussian_polynomial_limit μ hm hμ P
  have identify (ζ : Measure (Euclidean n)) (hζ : IsTangentAtInfinity m μ ζ) :
      (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖^2) ∂ζ) = l := by
    have huζ := isUnitUniform_of_tangentAtInfinity μ ζ hμ hζ
    obtain ⟨hreg, _, r, hr, hrinf, hlim⟩ := hζ
    have hseq (i : ℕ) := isUnitUniform_dimensionalBlowup μ hμ 0 hμ.2.1 (hr i)
    have hgauss := vague_integral_polynomial_mul_gaussian
      (fun i => dimensionalBlowup m μ 0 (r i)) ζ
      (fun i => (hseq i).1) hreg hlim 1 (m : ℝ)
      (fun i => IsUnitUniform.hasPolynomialGrowthBound _ (hseq i))
      (IsUnitUniform.hasPolynomialGrowthBound ζ huζ) P 1 zero_lt_one
    have hgauss' : Tendsto (fun i => ∫ z,
        MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖^2)
          ∂dimensionalBlowup m μ 0 (r i)) atTop
        (𝓝 (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖^2) ∂ζ)) := by
      simpa only [neg_one_mul] using hgauss
    exact tendsto_nhds_unique hgauss' (hl.comp hrinf)
  exact (identify ν hν).trans (identify ξ hξ).symm

theorem unique_tangent_at_infinity (hm : 0 < m) (hmn : m ≤ n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ ξ : Measure (Euclidean n), IsUnitUniform m ξ ∧
      ∀ ζ, IsTangentAtInfinity m ν ζ ↔ ζ = ξ := by
  obtain ⟨ξ, hξ, htξ⟩ := exists_unitUniform_tangentAtInfinity ν hν
  refine ⟨ξ, hξ, fun ζ => ⟨fun hζ =>
    tangentAtInfinity_eq_of_unitUniform hm ν ζ ξ hν hζ htξ, ?_⟩⟩
  rintro rfl
  exact htξ

theorem blowdown_sequence_converges (hm : 0 < m) (hmn : m ≤ n)
    (ν ξ : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hξ : IsTangentAtInfinity m ν ξ) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hrInfinity : Tendsto r atTop atTop) :
    Measure.WeaklyConverges (fun i => dimensionalBlowup m ν 0 (r i)) ξ := by
  intro f
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, ζ, hφ, hζ, hlim⟩ := exists_vague_subsequence_unitUniform
    (fun i => dimensionalBlowup m ν 0 (r (ns i)))
    (fun i => isUnitUniform_dimensionalBlowup ν hν 0 hν.2.1 (hr (ns i)))
  have htζ : IsTangentAtInfinity m ν ζ :=
    ⟨hζ.1, IsUnitUniform.ne_zero ζ hζ, fun i => r (ns (φ i)),
      fun i => hr (ns (φ i)), (hrInfinity.comp hns).comp hφ.tendsto_atTop, hlim⟩
  have heq := tangentAtInfinity_eq_of_unitUniform hm ν ζ ξ hν htζ hξ
  subst ζ
  exact ⟨φ, hlim f⟩

theorem tangent_at_infinity_conical (hm : 0 < m) (hmn : m ≤ n)
    (ν ξ : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (hξ : IsTangentAtInfinity m ν ξ) : IsConical m ξ := by
  intro s hs
  have huξ := isUnitUniform_of_tangentAtInfinity ν ξ hν hξ
  have hscaled := isUnitUniform_dimensionalBlowup ξ huξ 0 huξ.2.1 hs
  apply tangentAtInfinity_eq_of_unitUniform hm ν _ ξ hν _ hξ
  obtain ⟨hreg, _, r, hr, hrinf, hlim⟩ := hξ
  refine ⟨hscaled.1, IsUnitUniform.ne_zero _ hscaled, fun i => r i * s,
    fun i => mul_pos (hr i) hs, hrinf.atTop_mul_const hs, ?_⟩
  have hconv := vague_dimensionalBlowup_moving (m := m)
    (fun i => dimensionalBlowup m ν 0 (r i)) ξ
    (fun i => (isUnitUniform_dimensionalBlowup ν hν 0 hν.2.1 (hr i)).1)
    hreg hlim (fun _ => 0) 0 tendsto_const_nhds (fun _ => s) s
    (fun _ => hs) hs tendsto_const_nhds
  have hcompose (i : ℕ) :
      dimensionalBlowup m (dimensionalBlowup m ν 0 (r i)) 0 s =
        dimensionalBlowup m ν 0 (r i * s) := by
    simpa only [smul_zero, add_zero] using
      dimensionalBlowup_comp ν 0 0 (r i) s (hr i) hs
  simpa only [hcompose] using hconv

end Preiss
