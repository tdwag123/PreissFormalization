module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Tactic
@[expose] public section
open Filter
open scoped Topology
namespace Preiss
theorem quadratic_square_bound_of_bounded_offsets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (ω : E →L[ℝ] E →L[ℝ] F)
    (y : ℕ → E) (v : E) (hy : Tendsto y atTop (𝓝 v))
    (q : ℕ → F) (B : ℝ) (hB : 0 ≤ B)
    (hq : ∀ᶠ i in atTop, ‖q i‖ ≤ B)
    (herr : Tendsto (fun i => A (y i) (y i) + inner ℝ (ω (y i) (y i)) (q i))
      atTop (𝓝 0)) :
    (A v v)^2 ≤ B^2 * ‖ω v v‖^2 := by
  have hcA : Continuous (fun z => A z z) := A.continuous.clm_apply continuous_id
  have hcω : Continuous (fun z => ω z z) := ω.continuous.clm_apply continuous_id
  have hb : ∀ᶠ i in atTop, |A (y i) (y i)| ≤
      |A (y i) (y i) + inner ℝ (ω (y i) (y i)) (q i)| + B * ‖ω (y i) (y i)‖ := by
    filter_upwards [hq] with i hi
    have hinner := abs_real_inner_le_norm (ω (y i) (y i)) (q i)
    have htri := abs_add_le (A (y i) (y i) + inner ℝ (ω (y i) (y i)) (q i))
      (-inner ℝ (ω (y i) (y i)) (q i))
    simp only [add_neg_cancel_right, abs_neg] at htri
    have hnorm := mul_le_mul_of_nonneg_left hi (norm_nonneg (ω (y i) (y i)))
    nlinarith
  have hlim := tendsto_le_of_eventuallyLE ((hcA.tendsto v).comp hy).abs
    (herr.abs.add ((((hcω.tendsto v).comp hy).norm).const_mul B)) hb
  simp only [abs_zero, zero_add] at hlim
  have hs := (sq_le_sq₀ (abs_nonneg (A v v)) (mul_nonneg hB (norm_nonneg (ω v v)))).mpr hlim
  simpa only [sq_abs, mul_pow] using hs
end Preiss
