import Preiss.Analysis.Vague.ProjectionEnergy
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.UrysohnsLemma

/-! # Support constraints from vanishing weighted displacement energy

The weight can be any strictly positive continuous function. Integrability is
required only for the approximating measures; compact tests control the limit.
-/

open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported ENNReal
namespace Preiss
variable {n : ℕ}

theorem support_subset_fixedPoints_of_vague_of_weighted_projectionEnergy_tendsto_zero
    (w : Euclidean n → ℝ) (hw : Continuous w) (hwp : ∀ z, 0 < w z)
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (P : ℕ → (Euclidean n →L[ℝ] Euclidean n)) (Q : Euclidean n →L[ℝ] Euclidean n)
    (hPQ : Tendsto P atTop (𝓝 Q))
    (hint : ∀ i, Integrable (fun z => w z * ‖z - P i z‖ ^ 2) (μ i))
    (henergy : Tendsto (fun i => ∫ z, w z * ‖z - P i z‖ ^ 2 ∂μ i) atTop (𝓝 0)) :
    ν.support ⊆ {z | Q z = z} := by
  intro x hx
  obtain ⟨χ, hone, hcompact, _, hbounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (isCompact_singleton : IsCompact ({x} : Set (Euclidean n))) isOpen_univ
      (Set.subset_univ _)
  have hχcompact : HasCompactSupport (fun z => χ z) := hcompact
  let φ : C_c(Euclidean n, ℝ) :=
    ⟨⟨fun z => χ z * w z, χ.continuous.mul hw⟩, hχcompact.mul_right⟩
  have hφ (z : Euclidean n) : 0 ≤ φ z :=
    mul_nonneg (hbounds z).1 (hwp z).le
  have hlocal (i : ℕ) : Integrable (fun z => φ z * ‖z - P i z‖ ^ 2) (μ i) := by
    letI : (μ i).Regular := hμ i
    exact (φ.continuous.mul ((continuous_id.sub (P i).continuous).norm.pow 2)).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right
  have hbound (i : ℕ) : (∫ z, φ z * ‖z - P i z‖ ^ 2 ∂μ i) ≤
      ∫ z, w z * ‖z - P i z‖ ^ 2 ∂μ i := by
    apply integral_mono (hlocal i) (hint i)
    intro z
    change χ z * w z * ‖z - P i z‖ ^ 2 ≤ w z * ‖z - P i z‖ ^ 2
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbounds z).2 (hwp z).le
  have hconv := vague_integral_projectionEnergy_moving φ μ ν hμ hν hlim P Q hPQ
  have hzero : (∫ z, φ z * ‖z - Q z‖ ^ 2 ∂ν) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto hconv henergy (Eventually.of_forall hbound))
      (integral_nonneg fun z => mul_nonneg (hφ z) (sq_nonneg _))
  letI : ν.Regular := hν
  have hc : Continuous (fun z => φ z * ‖z - Q z‖ ^ 2) :=
    φ.continuous.mul ((continuous_id.sub Q.continuous).norm.pow 2)
  have hi : Integrable (fun z => φ z * ‖z - Q z‖ ^ 2) ν :=
    hc.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hae : (fun z => φ z * ‖z - Q z‖ ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_nonneg (hφ z) (sq_nonneg _)) hi).mp hzero
  have hsupp := Measure.support_subset_of_isClosed (μ := ν)
    (isClosed_eq hc continuous_const) hae
  have hxzero : φ x * ‖x - Q x‖ ^ 2 = 0 := hsupp hx
  have hχx : χ x = 1 := hone (Set.mem_singleton x)
  have hφx : 0 < φ x := by change 0 < χ x * w x; rw [hχx, one_mul]; exact hwp x
  have hnorm : ‖x - Q x‖ ^ 2 = 0 := (mul_eq_zero.mp hxzero).resolve_left hφx.ne'
  have hsub : x - Q x = 0 := norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm)
  exact (sub_eq_zero.mp hsub).symm
end Preiss
