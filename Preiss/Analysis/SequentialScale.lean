module
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-! # Uniform small-scale bounds from subsequence properties -/
@[expose] public section
open Filter Topology
namespace Preiss

theorem exists_uniform_scale_of_subsequence_property
    (P : ℝ → ℝ → Prop)
    (hmono : ∀ {a b r : ℝ}, 0 < a → a ≤ b → P b r → P a r)
    (hseq : ∀ (r : ℕ → ℝ), (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ a : ℝ, 0 < a ∧
        ∀ᶠ i in atTop, P a (r (φ i))) :
    ∃ a : ℝ, 0 < a ∧ ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, 0 < r → r < R → P a r := by
  classical
  by_contra h
  push_neg at h
  let ε (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)
  have hε (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose r hr hrε hbad using fun i => h (ε i) (hε i) (ε i) (hε i)
  have hr0 : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun i => (hr i).le) (fun i => (hrε i).le) hε0
  obtain ⟨φ, hφ, a, ha, hev⟩ := hseq r hr hr0
  have hsmall : ∀ᶠ i in atTop, ε (φ i) < a :=
    (hε0.comp hφ.tendsto_atTop).eventually_lt_const ha
  obtain ⟨i, hi, hia⟩ := (hev.and hsmall).exists
  exact hbad (φ i) (hmono (hε _) hia.le hi)

end Preiss
