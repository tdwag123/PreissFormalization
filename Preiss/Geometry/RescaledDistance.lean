module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Choose

/-! # Rescaled distances and approximate nearest points -/

@[expose] public section
open Metric Set Filter Topology
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_affine_rescale (a y z : E) {r : ℝ} (hr : 0 < r) :
    dist (a + r • y) z = r * dist y (r⁻¹ • (z - a)) := by
  have heq : a + r • y - z = r • (y - r⁻¹ • (z - a)) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm]

theorem exists_points_rescaled_tendsto_of_infDist
    (D : Set E) (hD : D.Nonempty) (a y : E) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hlim : Tendsto (fun i => infDist (a + r i • y) D / r i) atTop (𝓝 0)) :
    ∃ z : ℕ → E, (∀ i, z i ∈ D) ∧
      Tendsto (fun i => (r i)⁻¹ • (z i - a)) atTop (𝓝 y) := by
  classical
  have hchoose (i : ℕ) : ∃ z ∈ D,
      dist (a + r i • y) z < infDist (a + r i • y) D + r i / ((i : ℝ) + 1) := by
    apply (infDist_lt_iff hD).mp
    exact lt_add_of_pos_right _ (div_pos (hr i) (by positivity))
  choose z hz hdist using hchoose
  refine ⟨z, hz, ?_⟩
  have hbound (i : ℕ) : dist ((r i)⁻¹ • (z i - a)) y ≤
      infDist (a + r i • y) D / r i + 1 / ((i : ℝ) + 1) := by
    have hid : dist ((r i)⁻¹ • (z i - a)) y = dist (a + r i • y) (z i) / r i := by
      rw [dist_affine_rescale a y (z i) (hr i), mul_div_cancel_left₀ _ (hr i).ne', dist_comm]
    rw [hid]
    calc dist (a + r i • y) (z i) / r i ≤
        (infDist (a + r i • y) D + r i / ((i : ℝ) + 1)) / r i :=
          div_le_div_of_nonneg_right (hdist i).le (hr i).le
      _ = _ := by rw [add_div, div_right_comm (r i), div_self (hr i).ne']
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) hbound
    (by simpa using hlim.add tendsto_one_div_add_atTop_nhds_zero_nat)

end Preiss
