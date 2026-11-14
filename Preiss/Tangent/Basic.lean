import Preiss.Tangent.Defs
import Preiss.Tangent.Algebra
import Preiss.Tangent.BlowupSupport
import Preiss.Tangent.Continuity
import FormalizingGMT.TangentMeasures.Basic

/-! # Basic operations on dimensional tangents -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

theorem IsDimensionalTangent.isTangentMeasure
    {μ ν : Measure (Euclidean n)} {x : Euclidean n}
    (h : IsDimensionalTangent m μ ν x) : IsTangentMeasure μ ν x := by
  obtain ⟨hreg, hne, r, hr, hr0, hlim⟩ := h
  refine ⟨hreg, hne, r, fun i => (ENNReal.ofReal ((r i) ^ m))⁻¹,
    hr, ?_, ?_, hr0, hlim⟩
  · intro i
    exact ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  · intro i
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos (hr i) m)).ne'

theorem IsDimensionalTangent.smul
    {μ ν : Measure (Euclidean n)} {x : Euclidean n}
    (h : IsDimensionalTangent m μ ν x) {c : ℝ≥0∞}
    (hc : 0 < c) (hctop : c < ∞) :
    IsDimensionalTangent m (c • μ) (c • ν) x := by
  obtain ⟨hreg, hne, r, hr, hr0, hlim⟩ := h
  haveI : ν.Regular := hreg
  refine ⟨Measure.Regular.smul hctop.ne, ?_, r, hr, hr0, ?_⟩
  · intro hzero
    have heq := congrArg (fun ξ : Measure (Euclidean n) => c⁻¹ • ξ) hzero
    apply hne
    simpa [smul_smul, ENNReal.inv_mul_cancel hc.ne' hctop.ne] using heq
  · intro f
    have heq (i) := dimensionalBlowup_smul (m := m) μ x (r i) (hr i) c
    simp only [heq, integral_smul_measure, smul_eq_mul]
    exact tendsto_const_nhds.mul (hlim f)

theorem IsDimensionalTangent.dilate
    {μ ν : Measure (Euclidean n)} [IsLocallyFiniteMeasure μ] {x : Euclidean n}
    (h : IsDimensionalTangent m μ ν x) {s : ℝ} (hs : 0 < s) :
    IsDimensionalTangent m μ (dimensionalBlowup m ν 0 s) x := by
  obtain ⟨hreg, hne, r, hr, hr0, hlim⟩ := h
  refine ⟨regular_dimensionalBlowup ν hreg 0 hs, ?_,
    fun i => r i * s, fun i => mul_pos (hr i) hs, ?_, ?_⟩
  · intro hzero
    have heq := dimensionalBlowup_comp (m := m) ν 0 0 s s⁻¹ hs (inv_pos.mpr hs)
    rw [hzero] at heq
    have : ν = 0 := by simpa [dimensionalBlowup, hs.ne'] using heq.symm
    exact hne this
  · simpa using hr0.mul_const s
  · have hconv := vague_dimensionalBlowup_moving (m := m)
      (fun i => dimensionalBlowup m μ x (r i)) ν
      (fun i => regular_dimensionalBlowup μ inferInstance x (hr i)) hreg hlim
      (fun _ => 0) 0 tendsto_const_nhds (fun _ => s) s
      (fun _ => hs) hs tendsto_const_nhds
    simpa only [dimensionalBlowup_comp _ _ _ _ _ (hr _) hs, smul_zero, add_zero]
      using hconv

end Preiss
