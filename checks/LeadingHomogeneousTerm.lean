module
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section
open Filter Set
open scoped Topology BigOperators
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendsto_scaled_homogeneous_sum
    (A : (k : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (d : ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (y : ℕ → E) (v : E) (hy : Tendsto y atTop (𝓝 v)) :
    Tendsto (fun i => ∑ k ∈ Finset.range (d+1),
      (r i)^((k : ℝ)-(d : ℝ)) * A k (fun _ => y i)) atTop
      (𝓝 (A d (fun _ => v))) := by
  have heval (k : ℕ) : Tendsto (fun i => A k (fun _ => y i)) atTop
      (𝓝 (A k (fun _ => v))) :=
    (A k).cont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun _ => hy))
  have hlow : Tendsto (fun i => ∑ k ∈ Finset.range d,
      (r i)^((k : ℝ)-(d : ℝ)) * A k (fun _ => y i)) atTop (𝓝 0) := by
    have hterm (k : ℕ) (hk : k ∈ Finset.range d) :
        Tendsto (fun i => (r i)^((k : ℝ)-(d : ℝ)) * A k (fun _ => y i))
          atTop (𝓝 0) := by
      have hkd : (k : ℝ) < d := Nat.cast_lt.mpr (Finset.mem_range.mp hk)
      have hp := (tendsto_rpow_neg_atTop (sub_pos.mpr hkd)).comp hr
      have hp' : Tendsto (fun i => (r i)^((k : ℝ)-(d : ℝ))) atTop (𝓝 0) := by
        simpa only [show (k : ℝ)-(d : ℝ) = -((d : ℝ)-(k : ℝ)) by ring,
          Function.comp_def] using hp
      simpa using hp'.mul (heval k)
    simpa using tendsto_finsetSum (Finset.range d) hterm
  simpa only [Finset.sum_range_succ, sub_self, Real.rpow_zero, one_mul, zero_add]
    using hlow.add (heval d)

theorem leading_diagonal_nonneg_of_rescaled_points
    (A : (k : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (d : ℕ) (S : Set E)
    (hS : ∀ z ∈ S, 0 ≤ ∑ k ∈ Finset.range (d+1), A k (fun _ => z))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrinf : Tendsto r atTop atTop)
    (y : ℕ → E) (v : E) (hy : Tendsto y atTop (𝓝 v))
    (hmem : ∀ᶠ i in atTop, r i • y i ∈ S) : 0 ≤ A d (fun _ => v) := by
  apply ge_of_tendsto (tendsto_scaled_homogeneous_sum A d r hrinf y v hy)
  filter_upwards [hmem] with i hi
  have hpos := mul_nonneg (Real.rpow_nonneg (hr i).le (-(d : ℝ)))
    (hS (r i • y i) hi)
  have hscale (k : ℕ) :
      (r i)^(-(d : ℝ)) * A k (fun _ => r i • y i) =
        (r i)^((k : ℝ)-(d : ℝ)) * A k (fun _ => y i) := by
    rw [(A k).map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (hr i)]
    congr 2
    ring
  simpa only [Finset.mul_sum, hscale] using hpos

end Preiss
