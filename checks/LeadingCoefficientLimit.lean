import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic
open Filter Set Asymptotics
open scoped Topology
namespace Preiss

theorem tendsto_scaled_of_isLittleO_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (a : F) (k : ℕ)
    (h : IsLittleO (𝓝[>] (0 : ℝ))
      (fun s => f s - s ^ k • a) (fun s : ℝ => s ^ k)) :
    Tendsto (fun s => (s ^ k)⁻¹ • f s) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  have ht := h.tendsto_inv_smul_nhds_zero.add_const a
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero k (ne_of_gt hs)), one_smul,
    sub_add_cancel]

#print axioms tendsto_scaled_of_isLittleO_sub
end Preiss
