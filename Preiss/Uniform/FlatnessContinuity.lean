import Preiss.Uniform.Flatness
import Preiss.Uniform.FlatnessBasic
import Preiss.Uniform.FlatnessMinimum
import Preiss.Uniform.FlatnessVague
import Preiss.Geometry.FlatMeasure
import FormalizingGMT.WeakConvergence.Basic
import Mathlib.Topology.UrysohnsLemma

open MeasureTheory Metric Set Filter
open scoped Topology CompactlySupported
namespace Preiss
variable {n m : ℕ}

def IsFlatnessCutoff (φ : C_c(Euclidean n, ℝ)) : Prop :=
  (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
  (∀ z, ‖z‖ ≤ 1 → φ z = 1) ∧ tsupport φ ⊆ ball 0 2

theorem exists_flatnessCutoff (n : ℕ) :
    ∃ φ : C_c(Euclidean n, ℝ), IsFlatnessCutoff φ := by
  obtain ⟨f, hone, hcompact, hsupp, hbounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (isCompact_closedBall (0 : Euclidean n) 1) isOpen_ball
      (closedBall_subset_ball (one_lt_two : (1 : ℝ) < 2))
  refine ⟨⟨f, hcompact⟩, hbounds, ?_, hsupp⟩
  intro z hz
  change f z = 1
  exact hone (by simpa only [mem_closedBall, dist_zero_right] using hz)

theorem flatness_exists_minimizer (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) :
    ∃ V : Plane m n, flatness m φ μ = flatnessEnergy φ μ V ∧
      ∀ W : Plane m n, flatness m φ μ ≤ flatnessEnergy φ μ W := by
  letI : μ.Regular := hμ
  exact flatness_exists_minimizer_of_finite_on_compacts hmn φ μ

theorem flatness_nonneg (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ))
    (hφ : IsFlatnessCutoff φ) (μ : Measure (Euclidean n)) (hμ : μ.Regular) :
    0 ≤ flatness m φ μ := by
  exact flatness_nonneg_of_nonneg m φ (fun z => (hφ.1 z).1) μ

theorem flatness_eq_zero_of_isFlat (φ : C_c(Euclidean n, ℝ))
    (hφ : IsFlatnessCutoff φ) (μ : Measure (Euclidean n)) (hμ : IsFlat m μ) :
    flatness m φ μ = 0 := by
  exact flatness_eq_zero_of_isFlat_of_nonneg φ (fun z => (hφ.1 z).1) μ hμ

theorem exists_plane_ball_energy_le_of_flatness_le
    (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (ε : ℝ) (hε : flatness m φ μ ≤ ε) :
    ∃ V : Plane m n,
      (∫ z in ball 0 1, (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ) ≤ ε := by
  letI : μ.Regular := hμ
  obtain ⟨V, hV, _⟩ := flatness_exists_minimizer hmn φ hφ μ hμ
  refine ⟨V, ?_⟩
  calc
    (∫ z in ball 0 1, (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ) =
        ∫ z in ball 0 1, φ z * (infDist z (V.1 : Set (Euclidean n))) ^ 2 ∂μ := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change (infDist z (V.1 : Set (Euclidean n))) ^ 2 =
        φ z * (infDist z (V.1 : Set (Euclidean n))) ^ 2
      rw [hφ.2.1 z (by simpa only [dist_zero_right] using (mem_ball.mp hz).le), one_mul]
    _ ≤ flatnessEnergy φ μ V :=
      setIntegral_le_integral (integrable_flatnessEnergy_integrand φ μ V)
        (Filter.Eventually.of_forall fun z => mul_nonneg (hφ.1 z).1 (sq_nonneg _))
    _ = flatness m φ μ := hV.symm
    _ ≤ ε := hε

theorem flatness_continuous (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ))
    (hφ : IsFlatnessCutoff φ) (μ : ℕ → Measure (Euclidean n))
    (ν : Measure (Euclidean n)) (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) :
    Tendsto (fun i => flatness m φ (μ i)) atTop (𝓝 (flatness m φ ν)) := by
  exact flatness_tendsto_of_vague hmn φ μ ν hμ hν hlim

end Preiss
