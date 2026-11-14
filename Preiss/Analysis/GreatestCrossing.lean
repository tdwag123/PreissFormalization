module
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
open Set
namespace Preiss

theorem exists_greatest_crossing (f : ℝ → ℝ) (a b ε : ℝ)
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (ha : ε < f a) (hb : f b < ε) :
    ∃ c ∈ Ioo a b, f c = ε ∧ ∀ t ∈ Icc c b, f t ≤ ε := by
  sorry

end Preiss
