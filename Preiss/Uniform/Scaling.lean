module

public import Preiss.Uniform.Defs
public import Preiss.Tangent.Algebra
public import Preiss.Tangent.BlowupSupport
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-! # Uniform ball constants and changes of centre and scale

The uncentered predicate explicitly requires nonempty support. In particular,
`infDist 0 μ.support = 0` cannot accidentally admit the zero measure.
-/

@[expose] public section
open MeasureTheory Metric Set Topology
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

/-- An uncentered regular uniform measure with a specified positive ball constant. -/
def IsUniformWithConstant (m : ℕ) (q : ℝ) (μ : Measure (Euclidean n)) : Prop :=
  μ.Regular ∧ μ.support.Nonempty ∧ 0 < q ∧
    ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (closedBall x r) = ENNReal.ofReal (q * r ^ m)

theorem isUnitUniform_iff_constant_one (μ : Measure (Euclidean n)) :
    IsUnitUniform m μ ↔ IsUniformWithConstant m 1 μ ∧ (0 : Euclidean n) ∈ μ.support := by
  constructor
  · rintro ⟨hreg, hzero, hball⟩
    refine ⟨⟨hreg, ⟨0, hzero⟩, zero_lt_one, ?_⟩, hzero⟩
    simpa only [one_mul] using hball
  · rintro ⟨⟨hreg, _, _, hball⟩, hzero⟩
    exact ⟨hreg, hzero, by simpa only [one_mul] using hball⟩

theorem uniformWithConstant_dimensionalBlowup (μ : Measure (Euclidean n))
    {q : ℝ} (hμ : IsUniformWithConstant m q μ) (a : Euclidean n)
    {r : ℝ} (hr : 0 < r) :
    IsUniformWithConstant m q (dimensionalBlowup m μ a r) := by
  refine ⟨regular_dimensionalBlowup μ hμ.1 a hr, ?_, hμ.2.2.1, ?_⟩
  · rw [dimensionalBlowup_support μ a hr]
    exact hμ.2.1.image _
  · intro x hx ρ hρ
    rw [dimensionalBlowup_support μ a hr] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hkey (z : Euclidean n) : r⁻¹ • (z - a) - r⁻¹ • (y - a) = r⁻¹ • (z - y) := by
      rw [← smul_sub]
      congr 1
      abel
    have hpre : (fun z : Euclidean n ↦ r⁻¹ • (z - a)) ⁻¹'
        closedBall (r⁻¹ • (y - a)) ρ = closedBall y (r * ρ) := by
      ext z
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, hkey, norm_smul,
        norm_inv, Real.norm_eq_abs, abs_of_pos hr]
      rw [inv_mul_le_iff₀ hr]
    have hmap : Measurable (fun z : Euclidean n ↦ r⁻¹ • (z - a)) :=
      ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
    rw [dimensionalBlowup, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hmap measurableSet_closedBall, hpre,
      hμ.2.2.2 y hy (r * ρ) (mul_pos hr hρ)]
    have hreal : q * (r * ρ) ^ m = r ^ m * (q * ρ ^ m) := by rw [mul_pow]; ring
    rw [hreal, ENNReal.ofReal_mul (pow_nonneg hr.le m), ← mul_assoc,
      ENNReal.inv_mul_cancel ((ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne')
        ENNReal.ofReal_ne_top, one_mul]

theorem isUnitUniform_dimensionalBlowup (μ : Measure (Euclidean n))
    (hμ : IsUnitUniform m μ) (a : Euclidean n) (ha : a ∈ μ.support)
    {r : ℝ} (hr : 0 < r) :
    IsUnitUniform m (dimensionalBlowup m μ a r) := by
  apply (isUnitUniform_iff_constant_one _).mpr
  refine ⟨uniformWithConstant_dimensionalBlowup μ
    ((isUnitUniform_iff_constant_one μ).mp hμ).1 a hr, ?_⟩
  rw [dimensionalBlowup_support μ a hr]
  exact ⟨a, ha, by simp⟩

theorem uniformWithConstant_smul (μ : Measure (Euclidean n))
    {q c : ℝ} (hμ : IsUniformWithConstant m q μ) (hc : 0 < c) :
    IsUniformWithConstant m (c * q) (ENNReal.ofReal c • μ) := by
  have : μ.Regular := hμ.1
  have hsupport : (ENNReal.ofReal c • μ).support = μ.support := by
    ext x
    simp only [Measure.mem_support_iff_forall, Measure.smul_apply, smul_eq_mul,
      ENNReal.mul_pos_iff, ENNReal.ofReal_pos.mpr hc, true_and]
  refine ⟨Measure.Regular.smul ENNReal.ofReal_ne_top, hsupport.symm ▸ hμ.2.1,
    mul_pos hc hμ.2.2.1, ?_⟩
  intro x hx r hr
  rw [hsupport] at hx
  rw [Measure.smul_apply, smul_eq_mul, hμ.2.2.2 x hx r hr,
    ← ENNReal.ofReal_mul hc.le, mul_assoc]

end Preiss
