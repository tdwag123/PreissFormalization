module
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

@[expose] public section
open Set
namespace Preiss

theorem exists_greatest_crossing (f : ℝ → ℝ) (a b ε : ℝ)
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (ha : ε < f a) (hb : f b < ε) :
    ∃ c ∈ Ioo a b, f c = ε ∧ ∀ t ∈ Icc c b, f t ≤ ε := by
  let S := Icc a b ∩ f ⁻¹' {ε}
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hne : S.Nonempty := by
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab.le hf ⟨hb.le, ha.le⟩
    exact ⟨x, hx, hfx⟩
  obtain ⟨c, hc, hmax⟩ := hcompact.exists_isGreatest hne
  have hfc : f c = ε := hc.2
  have hac : a < c := lt_of_le_of_ne hc.1.1 (by
    intro h; subst c; exact ha.ne' hfc)
  have hcb : c < b := lt_of_le_of_ne hc.1.2 (by
    intro h; subst c; exact hb.ne hfc)
  refine ⟨c, ⟨hac,hcb⟩, hfc, ?_⟩
  intro t ht
  by_contra hnot
  have hft : ε < f t := lt_of_not_ge hnot
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc (hac.le.trans ht.1) le_rfl
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' ht.2 (hf.mono hsub) ⟨hb.le,hft.le⟩
  have htu : t < u := lt_of_le_of_ne hu.1 (by
    intro h; subst u; exact hft.ne' hfu)
  have huc : u ≤ c := hmax ⟨hsub hu, hfu⟩
  exact (not_lt_of_ge huc) (lt_of_le_of_lt ht.1 htu)

end Preiss
