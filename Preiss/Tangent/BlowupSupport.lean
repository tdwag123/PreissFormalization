module
public import Preiss.Tangent.Blowup
public import Preiss.Analysis.MeasureSupport
public import Mathlib.Topology.Algebra.ConstMulAction

/-! # Support and regularity of dimensionally normalized blow-ups -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem dimensionalBlowup_support (μ : Measure (Euclidean n)) (a : Euclidean n)
    {r : ℝ} (hr : 0 < r) :
    (dimensionalBlowup m μ a r).support =
      (fun y ↦ r⁻¹ • (y - a)) '' μ.support := by
  unfold dimensionalBlowup
  rw [measure_support_smul _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)]
  let e : Euclidean n ≃ₜ Euclidean n :=
    (Homeomorph.subRight a).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  exact measure_support_map_homeomorph e μ

theorem regular_dimensionalBlowup (μ : Measure (Euclidean n)) (hμ : μ.Regular)
    (a : Euclidean n) {r : ℝ} (hr : 0 < r) :
    (dimensionalBlowup m μ a r).Regular := by
  have : μ.Regular := hμ
  let e : Euclidean n ≃ₜ Euclidean n :=
    (Homeomorph.subRight a).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have : (μ.map e).Regular := Measure.Regular.map e
  change ((ENNReal.ofReal (r ^ m))⁻¹ • μ.map e).Regular
  exact Measure.Regular.smul (ENNReal.inv_ne_top.mpr
    ((ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'))

end Preiss
