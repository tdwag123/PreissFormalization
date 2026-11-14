module

public import Preiss.Analysis.Vague.CompactTests
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Moving squared-projection integrals under vague convergence -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem vague_integral_projectionEnergy_moving
    (φ : C_c(Euclidean n, ℝ)) (μ : ℕ → Measure (Euclidean n))
    (ν : Measure (Euclidean n)) (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (P : ℕ → (Euclidean n →L[ℝ] Euclidean n)) (Q : Euclidean n →L[ℝ] Euclidean n)
    (hPQ : Tendsto P atTop (𝓝 Q)) :
    Tendsto (fun i => ∫ z, φ z * ‖z - P i z‖ ^ 2 ∂μ i) atTop
      (𝓝 (∫ z, φ z * ‖z - Q z‖ ^ 2 ∂ν)) := by
  let F (T : Euclidean n →L[ℝ] Euclidean n) (z : Euclidean n) := φ z * ‖z - T z‖ ^ 2
  let g (T : Euclidean n →L[ℝ] Euclidean n) : C_c(Euclidean n, ℝ) :=
    { toContinuousMap := ⟨F T, by dsimp [F]; fun_prop⟩
      hasCompactSupport' := φ.hasCompactSupport.mul_right }
  let K := tsupport φ
  have hK : IsCompact K := φ.hasCompactSupport
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hzero (T : Euclidean n →L[ℝ] Euclidean n) (z : Euclidean n) (hz : z ∉ K) :
      g T z = 0 := by
    change φ z * ‖z - T z‖ ^ 2 = 0
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hF : Continuous (fun w : (Euclidean n →L[ℝ] Euclidean n) × K => F w.1 w.2) := by
    dsimp [F]
    fun_prop
  have hunif : ∀ ε > 0, ∀ᶠ i in atTop, ∀ z, |g (P i) z - g Q z| < ε := by
    intro ε hε
    have hlocal := Metric.tendstoUniformly_iff.mp
      (Continuous.tendstoUniformly (fun T => fun z : K => F T z) hF Q) ε hε
    filter_upwards [hPQ.eventually hlocal] with i hi
    intro z
    by_cases hz : z ∈ K
    · change |F (P i) z - F Q z| < ε
      simpa only [Real.dist_eq, abs_sub_comm] using hi (⟨z, hz⟩ : K)
    · rw [hzero (P i) z hz, hzero Q z hz, sub_self, abs_zero]
      exact hε
  exact vague_integral_moving_compact_test μ ν hμ hν hlim K hK (fun i => g (P i))
    (g Q) (fun i => hzero (P i)) (hzero Q) hunif

end Preiss
