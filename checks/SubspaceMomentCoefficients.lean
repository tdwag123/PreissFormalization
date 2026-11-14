import Preiss.Uniform.SubspaceMomentTrace
import Preiss.Uniform.MomentCoefficients
import Preiss.Uniform.MomentEstimates
import Preiss.Analysis.TaylorShift
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Tactic

open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
namespace Preiss
variable {n m : ℕ}

theorem gaussianMoment_taylor_remainder_map
    (μ : Measure (Euclidean n)) (B : MomentCoefficientFamily n)
    (hB : IsMomentExpansion μ B) (k : ℕ) (hk : 0 < k)
    (L : MomentForm n k →L[ℝ] ℝ) (q : ℕ) (hq : 0 < q) :
    IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => L (gaussianMomentForm μ k s) -
        ∑ i ∈ Finset.range q, (s^(i+1) / ((i+1).factorial : ℝ)) * L (B k (i+1)))
      (fun s : ℝ => s^q) := by
  have h := (ContinuousLinearMap.isBigO_comp (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (F := MomentForm n k) (G := ℝ) L
    (fun s => gaussianMomentForm μ k s - momentTaylorPolynomial B k q s)
    (𝓝[>] (0 : ℝ))).trans_isLittleO (hB.2 k hk q hq)
  simpa only [map_sub, momentTaylorPolynomial, map_sum, map_smul, smul_eq_mul] using h

theorem subspaceTrace_secondCoefficient_of_cylinder
    (μ : Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (U : Submodule ℝ (Euclidean n)) (b : Euclidean n)
    (hcyl : ∀ᵐ z ∂μ, ‖U.starProjection z‖^2 = 2 * inner ℝ b z) :
    bilinearTrace (restrictBilinear (momentBilinear (B 2 2)) U) =
      4 * B 1 1 (fun _ => b) := by
  let E : MomentForm n 1 →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euclidean n) ℝ (fun _ => b)
  let L := subspaceMomentTraceCLM U
  have hf : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => gaussianMomentForm μ 1 s (fun _ => b) - s * B 1 1 (fun _ => b))
      (fun s : ℝ => s) := by
    simpa [E, Finset.sum_range_succ] using
      gaussianMoment_taylor_remainder_map μ B hB 1 zero_lt_one E 1 zero_lt_one
  have hg : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => L (gaussianMomentForm μ 2 s) - s * L (B 2 1) - (s^2/2)*L (B 2 2))
      (fun s : ℝ => s^2) := by
    have h := gaussianMoment_taylor_remainder_map μ B hB 2 (by decide) L 2 (by decide)
    convert h using 1
    funext s
    norm_num [Finset.sum_range_succ]
    ring
  have heq : ∀ᶠ s in 𝓝[>] (0 : ℝ), L (gaussianMomentForm μ 2 s) =
      2*s*gaussianMomentForm μ 1 s (fun _ => b) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact subspaceTrace_gaussianMoment_of_cylinder U μ b s
      (integrable_gaussianMomentKernel μ hm hμ 1 s hs)
      (integrable_gaussianMomentKernel μ hm hμ 2 s hs) hcyl
  have h := first_second_taylor_coefficients_of_mul_scale
    (fun s => gaussianMomentForm μ 1 s (fun _ => b))
    (fun s => L (gaussianMomentForm μ 2 s))
    (B 1 1 (fun _ => b)) (L (B 2 1)) (L (B 2 2)) 2 hf hg heq
  simpa only [L, subspaceMomentTraceCLM_apply, show (2:ℝ)*2=4 by norm_num] using h.2

end Preiss
#print axioms Preiss.gaussianMoment_taylor_remainder_map
#print axioms Preiss.subspaceTrace_secondCoefficient_of_cylinder
