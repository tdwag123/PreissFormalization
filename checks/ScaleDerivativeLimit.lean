import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Tactic
open Filter Set
open scoped Topology
namespace Preiss

theorem scale_derivative_limit_eq_zero
    (f f' : ℝ → ℝ) (a L : ℝ)
    (hd : ∀ᶠ s in 𝓝[>] (0 : ℝ), HasDerivAt f (f' s) s)
    (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 a))
    (hL : Tendsto (fun s => s * f' s) (𝓝[>] (0 : ℝ)) (𝓝 L)) : L = 0 := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hnum : Tendsto (fun s => s * f s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hid.mul hf
  have hquot : Tendsto (fun s => (s * f s) / s) (𝓝[>] (0 : ℝ)) (𝓝 (a + L)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (f' := fun s => f s + s * f' s)
      (g' := fun _ => (1 : ℝ)) ?_ ?_ ?_ hnum hid ?_
    · filter_upwards [hd] with s hs
      simpa only [one_mul] using (hasDerivAt_id s).mul hs
    · exact Eventually.of_forall fun s => hasDerivAt_id s
    · exact Eventually.of_forall fun _ => one_ne_zero
    · simpa only [div_one] using hf.add hL
  have hquot' : Tendsto (fun s => (s * f s) / s) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    apply hf.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (mul_div_cancel_left₀ (f s) (ne_of_gt hs)).symm
  have h := tendsto_nhds_unique hquot hquot'
  linarith

#print axioms scale_derivative_limit_eq_zero
end Preiss
