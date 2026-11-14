module
public import Preiss.Uniform.MomentEstimates
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section
open MeasureTheory Filter Set Asymptotics
open scoped Topology
namespace Preiss
variable {n m : ℕ}

theorem gaussianMoment_isBigO_rpow (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (k : ℕ) (hk : 0 < k) :
    IsBigO (𝓝[>] (0 : ℝ)) (gaussianMomentForm μ k) (fun s : ℝ => s ^ ((k : ℝ) / 2)) := by
  obtain ⟨C, hC, hbound⟩ := norm_gaussianMomentForm_le (n := n) hm
  apply IsBigO.of_bound (C * 2 ^ k * (k : ℝ) ^ ((k : ℝ) / 2) / (k.factorial : ℝ))
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt (show 0 < s from hs)) _)]
  convert hbound μ hμ k hk s hs using 1 <;> ring

end Preiss
