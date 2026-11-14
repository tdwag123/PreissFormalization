module

public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Maps.Basic

/-! # Metrics from countably many separating real coordinates

The exact weighted truncation matches the countable-test distance used for vague measures.
The construction and convergence theorem apply to arbitrary types and arbitrary filters.
-/

@[expose] public section
open Filter Topology
open scoped PiCountable
namespace Preiss
variable {A B : Type*}

/-- Shift by one coordinate so the product metric has exactly the desired weights. -/
noncomputable def countableCoordinateMap (f : ℕ → A → ℝ) (a : A) : ℕ → ℝ
  | 0 => 0
  | j + 1 => (2 : ℝ)⁻¹ ^ (j + 1) * f j a

theorem countableCoordinateMap_injective (f : ℕ → A → ℝ)
    (hsep : ∀ a b, (∀ j, f j a = f j b) → a = b) :
    Function.Injective (countableCoordinateMap f) := by
  intro a b hab
  apply hsep a b
  intro j
  have h := congrFun hab (j + 1)
  change (2 : ℝ)⁻¹ ^ (j + 1) * f j a = (2 : ℝ)⁻¹ ^ (j + 1) * f j b at h
  exact mul_left_cancel₀ (by positivity : (2 : ℝ)⁻¹ ^ (j + 1) ≠ 0) h

/-- Any countable separating real coordinate family induces this bounded metric. -/
@[instance_reducible]
noncomputable def countableCoordinateMetric (f : ℕ → A → ℝ)
    (hsep : ∀ a b, (∀ j, f j a = f j b) → a = b) : MetricSpace A :=
  MetricSpace.induced (countableCoordinateMap f)
    (countableCoordinateMap_injective f hsep) PiCountable.metricSpace

theorem countableCoordinateMetric_dist (f : ℕ → A → ℝ)
    (hsep : ∀ a b, (∀ j, f j a = f j b) → a = b) (a b : A) :
    letI := countableCoordinateMetric f hsep
    dist a b = ∑' j : ℕ, (2 : ℝ)⁻¹ ^ (j + 1) * min 1 |f j a - f j b| := by
  letI : MetricSpace (ℕ → ℝ) := PiCountable.metricSpace
  change dist (countableCoordinateMap f a) (countableCoordinateMap f b) = _
  rw [PiCountable.dist_eq_tsum,
    (PiCountable.dist_summable (countableCoordinateMap f a)
      (countableCoordinateMap f b)).tsum_eq_zero_add]
  simp only [countableCoordinateMap, Encodable.encode_nat, dist_self, pow_zero,
    min_eq_right (by norm_num : (0 : ℝ) ≤ 1), zero_add]
  apply tsum_congr
  intro j
  rw [Real.dist_eq, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ (j + 1)),
    mul_min_of_nonneg 1 |f j a - f j b| (by positivity)]
  rw [mul_one]

theorem countableCoordinateMetric_tendsto_iff (f : ℕ → A → ℝ)
    (hsep : ∀ a b, (∀ j, f j a = f j b) → a = b)
    (g : B → A) (l : Filter B) (a : A) :
    letI := countableCoordinateMetric f hsep
    Tendsto g l (𝓝 a) ↔ ∀ j, Tendsto (fun b => f j (g b)) l (𝓝 (f j a)) := by
  letI : MetricSpace (ℕ → ℝ) := PiCountable.metricSpace
  letI := countableCoordinateMetric f hsep
  have hemb : Topology.IsEmbedding (countableCoordinateMap f) :=
    (countableCoordinateMap_injective f hsep).isEmbedding_induced
  rw [hemb.tendsto_nhds_iff, tendsto_pi_nhds]
  constructor
  · intro h j
    have hw : (2 : ℝ)⁻¹ ^ (j + 1) ≠ 0 := by positivity
    have hj := (h (j + 1)).const_mul (((2 : ℝ)⁻¹ ^ (j + 1))⁻¹)
    simpa only [Function.comp_apply, countableCoordinateMap, ← mul_assoc,
      inv_mul_cancel₀ hw, one_mul] using hj
  · intro h j
    cases j with
    | zero => exact tendsto_const_nhds
    | succ j =>
        simpa only [Function.comp_apply, countableCoordinateMap] using
          (h j).const_mul ((2 : ℝ)⁻¹ ^ (j + 1))

end Preiss
