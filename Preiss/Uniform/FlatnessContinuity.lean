import Preiss.Uniform.Flatness
import Preiss.Uniform.FlatnessBasic
import Preiss.Geometry.FlatMeasure
import FormalizingGMT.WeakConvergence.Basic

open MeasureTheory Metric Set Filter
open scoped Topology CompactlySupported
namespace Preiss
variable {n m : ℕ}

def IsFlatnessCutoff (φ : C_c(Euclidean n, ℝ)) : Prop :=
  (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
  (∀ z, ‖z‖ ≤ 1 → φ z = 1) ∧ tsupport φ ⊆ ball 0 2

theorem exists_flatnessCutoff (n : ℕ) :
    ∃ φ : C_c(Euclidean n, ℝ), IsFlatnessCutoff φ := by
  sorry

theorem flatness_exists_minimizer (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) :
    ∃ V : Plane m n, flatness m φ μ = flatnessEnergy φ μ V ∧
      ∀ W : Plane m n, flatness m φ μ ≤ flatnessEnergy φ μ W := by
  sorry

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
  sorry

theorem flatness_continuous (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ))
    (hφ : IsFlatnessCutoff φ) (μ : ℕ → Measure (Euclidean n))
    (ν : Measure (Euclidean n)) (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) :
    Tendsto (fun i => flatness m φ (μ i)) atTop (𝓝 (flatness m φ ν)) := by
  sorry

end Preiss
