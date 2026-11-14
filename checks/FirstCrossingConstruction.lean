import Preiss.Theorem.FirstCrossing
import Preiss.Tangent.Flatness
import Preiss.Tangent.Extraction
import Preiss.Analysis.GreatestCrossing
import Mathlib.Tactic

open MeasureTheory Metric Set Filter
open scoped Topology CompactlySupported
namespace Preiss
variable {n m : ℕ}

theorem exists_first_crossing_sequences_of_flatness_gt
    (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x)
    (hu : ∀ ν, IsDimensionalTangent m μ ν x → IsUnitUniform m ν)
    (α ζ : Measure (Euclidean n)) (hα : IsDimensionalTangent m μ α x)
    (hαflat : IsFlat m α) (hζ : IsDimensionalTangent m μ ζ x)
    (hζgt : ε < flatness m φ ζ) :
    ∃ (ξ : Measure (Euclidean n)) (r σ : ℕ → ℝ), IsUnitUniform m ξ ∧
      IsDimensionalTangent m μ ξ x ∧ FirstCrossingData m μ x φ ε α ξ r σ := by
  classical
  let f : ℝ → ℝ := fun t => flatness m φ (dimensionalBlowup m μ x t)
  have hμ : μ.Regular := inferInstance
  have hcont : ContinuousOn f (Ioi 0) :=
    continuousOn_flatness_dimensionalBlowup hmn φ hφ μ hμ x
  obtain ⟨r₀, hr₀pos, hr₀zero, hr₀lim⟩ := hα.2.2
  obtain ⟨t, htpos, htzero, htlim⟩ := hζ.2.2
  have hrf : Tendsto (fun i => f (r₀ i)) atTop (𝓝 0) := by
    have hh := flatness_continuous hmn φ hφ _ _
      (fun i => regular_dimensionalBlowup μ hμ x (hr₀pos i)) hα.1 hr₀lim
    simpa only [flatness_eq_zero_of_isFlat φ hφ α hαflat] using hh
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrf.eventually_lt_const hε)
  let r (i : ℕ) := r₀ (i + N)
  have hrpos (i : ℕ) : 0 < r i := hr₀pos (i+N)
  have hrzero : Tendsto r atTop (𝓝 0) := hr₀zero.comp (tendsto_add_atTop_nat N)
  have hrlim : Measure.WeaklyConverges (fun i => dimensionalBlowup m μ x (r i)) α :=
    fun g => (hr₀lim g).comp (tendsto_add_atTop_nat N)
  have hrsmall (i : ℕ) : f (r i) < ε := hN (i+N) (by omega)
  have htf : Tendsto (fun i => f (t i)) atTop (𝓝 (flatness m φ ζ)) :=
    flatness_continuous hmn φ hφ _ _
      (fun i => regular_dimensionalBlowup μ hμ x (htpos i)) hζ.1 htlim
  have hchoose (i : ℕ) : ∃ j, t j < r i ∧ ε < f (t j) :=
    ((htzero.eventually_lt_const (hrpos i)).and (htf.eventually_gt_const hζgt)).exists
  choose j hjrad hjlarge using hchoose
  have hcross (i : ℕ) : ∃ c ∈ Ioo (t (j i)) (r i), f c = ε ∧
      ∀ u ∈ Icc c (r i), f u ≤ ε :=
    exists_greatest_crossing f (t (j i)) (r i) ε (hjrad i)
      (hcont.mono (fun u hu => lt_of_lt_of_le (htpos (j i)) hu.1))
      (hjlarge i) (hrsmall i)
  choose σ hσmem hσeq hσinterval using hcross
  have hσpos (i : ℕ) : 0 < σ i := (htpos (j i)).trans (hσmem i).1
  have hσle (i : ℕ) : σ i ≤ r i := (hσmem i).2.le
  have hσzero : Tendsto σ atTop (𝓝 0) :=
    squeeze_zero (fun i => (hσpos i).le) hσle hrzero
  obtain ⟨τ, ξ, hτ, hξreg, hξne, hξlim, _⟩ :=
    exists_dimensional_tangent_subseq_of_density_bounds μ x hd.densities σ hσpos hσzero
  have hξdim : IsDimensionalTangent m μ ξ x :=
    ⟨hξreg, hξne, σ ∘ τ, fun i => hσpos (τ i), hσzero.comp hτ.tendsto_atTop, hξlim⟩
  have hξflat : flatness m φ ξ = ε := by
    have hh := flatness_continuous hmn φ hφ _ _
      (fun i => regular_dimensionalBlowup μ hμ x (hσpos (τ i))) hξreg hξlim
    have heq : (fun i => flatness m φ (dimensionalBlowup m μ x (σ (τ i)))) =
        (fun _ : ℕ => ε) := by
      funext i
      exact hσeq (τ i)
    rw [heq] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  refine ⟨ξ, r ∘ τ, σ ∘ τ, hu ξ hξdim, hξdim, ?_⟩
  refine ⟨fun i => ⟨hσpos (τ i), hσle (τ i)⟩, hrzero.comp hτ.tendsto_atTop,
    fun g => (hrlim g).comp hτ.tendsto_atTop, hξlim, hξflat, ?_, ?_⟩
  · intro i
    exact hσeq (τ i)
  · intro i u hu
    exact hσinterval (τ i) u hu

end Preiss

#print axioms Preiss.exists_first_crossing_sequences_of_flatness_gt
