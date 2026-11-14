import Preiss.Tangent.Compactness
import Preiss.Uniform.FlatPseudotangent
import Preiss.Geometry.UnitFlat

/-! # A flat dimensional tangent from uniform recentering

The common ball constant is preserved through the whole scaling-orbit limit.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem exists_flat_dimensionalTangent_of_uniform_recenter
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (ν : Measure (Euclidean n)) {q : ℝ} (hν : IsUniformWithConstant m q ν)
    (h0 : (0 : Euclidean n) ∈ ν.support)
    (hrec : ∀ y ∈ ν.support, ∀ r : ℝ, 0 < r →
      IsDimensionalTangent m μ (dimensionalBlowup m ν y r) x) :
    ∃ V : Plane m n, IsDimensionalTangent m μ (ENNReal.ofReal q • unitFlat V) x := by
  let C : ℝ≥0∞ := ENNReal.ofReal q
  have hq : 0 < q := hν.2.2.1
  have hC : 0 < C := ENNReal.ofReal_pos.mpr hq
  have hCfin : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hCinv : C⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hCfin
  let τ : Measure (Euclidean n) := C⁻¹ • ν
  have hτ : IsUnitUniform m τ := by
    apply (isUnitUniform_iff_constant_one τ).mpr
    constructor
    · have hu := uniformWithConstant_smul ν hν (inv_pos.mpr hq)
      simpa only [τ, C, ENNReal.ofReal_inv_of_pos hq, inv_mul_cancel₀ hq.ne'] using hu
    · change (0 : Euclidean n) ∈ (C⁻¹ • ν).support
      rw [measure_support_smul ν hCinv]
      exact h0
  have hback : C • τ = ν := by
    simp only [τ, smul_smul, ENNReal.mul_inv_cancel hC.ne' hCfin, one_smul]
  obtain ⟨V, a, r, ha, hr, hlim⟩ := uniform_has_flat_pseudotangent hm hmn τ hτ
  have haν (i : ℕ) : a i ∈ ν.support := by
    have hi := ha i
    change a i ∈ (C⁻¹ • ν).support at hi
    rwa [measure_support_smul ν hCinv] at hi
  have hseq (i : ℕ) : dimensionalBlowup m ν (a i) (r i) =
      C • dimensionalBlowup m τ (a i) (r i) := by
    rw [← dimensionalBlowup_smul τ (a i) (r i) (hr i).1 C, hback]
  have hscaled : Measure.WeaklyConverges
      (fun i => dimensionalBlowup m ν (a i) (r i)) (C • unitFlat V) := by
    intro f
    simp only [hseq, integral_smul_measure, smul_eq_mul]
    exact tendsto_const_nhds.mul (hlim f)
  letI : (unitFlat V).Regular := regular_unitFlat V
  have hreg : (C • unitFlat V).Regular := Measure.Regular.smul hCfin
  have hne : C • unitFlat V ≠ 0 := by
    intro hz
    have hcancel := congrArg (fun η : Measure (Euclidean n) => C⁻¹ • η) hz
    have hz' : unitFlat V = 0 := by
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC.ne' hCfin, one_smul, smul_zero] using hcancel
    exact unitFlat_ne_zero V hz'
  exact ⟨V, dimensionalTangent_closed μ x _ _
    (fun i => hrec (a i) (haν i) (r i) (hr i).1) hscaled hreg hne⟩

end Preiss
