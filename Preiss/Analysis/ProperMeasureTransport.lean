module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.Maps.Proper.Basic

/-! # Support and regularity under closed and proper maps -/

@[expose] public section
open MeasureTheory Set Filter Topology
namespace Preiss
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem measure_support_map_of_continuous_of_isClosedMap
    (f : X → Y) (hf : Continuous f) (hclosed : IsClosedMap f)
    (μ : Measure X) (hμ : μ.Regular) : (μ.map f).support = f '' μ.support := by
  classical
  letI : μ.Regular := hμ
  ext y
  rw [Measure.support_eq_forall_isOpen (μ := μ.map f)]
  constructor
  · intro hy
    by_contra hy'
    have hopen : IsOpen (f '' μ.support)ᶜ :=
      (hclosed _ Measure.isClosed_support).isOpen_compl
    have hpos := hy _ hy' hopen
    rw [Measure.map_apply hf.measurable hopen.measurableSet] at hpos
    have hsub : f ⁻¹' (f '' μ.support)ᶜ ⊆ μ.supportᶜ := by
      intro x hx hxs
      exact hx ⟨x, hxs, rfl⟩
    have hzero := measure_mono_null hsub (Measure.measure_compl_support_of_regular (μ := μ))
    exact (ne_of_gt hpos) hzero
  · rintro ⟨x, hx, rfl⟩ U hxU hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    rw [Measure.support_eq_forall_isOpen] at hx
    exact hx (f ⁻¹' U) hxU (hU.preimage hf)

theorem outerRegular_map_of_continuous_of_isClosedMap
    (f : X → Y) (hf : Continuous f) (hclosed : IsClosedMap f)
    (μ : Measure X) (hμ : μ.OuterRegular) : (μ.map f).OuterRegular := by
  classical
  letI : μ.OuterRegular := hμ
  refine ⟨fun A hA r hr => ?_⟩
  rw [Measure.map_apply hf.measurable hA] at hr
  obtain ⟨U, hAU, hU, hmass⟩ := Set.exists_isOpen_lt_of_lt (f ⁻¹' A) r hr
  have hopen : IsOpen (f '' Uᶜ)ᶜ := (hclosed _ hU.isClosed_compl).isOpen_compl
  have hAV : A ⊆ (f '' Uᶜ)ᶜ := by
    intro y hy
    rintro ⟨x, hx, hxy⟩
    apply hx
    apply hAU
    change f x ∈ A
    simpa only [hxy] using hy
  have hpre : f ⁻¹' (f '' Uᶜ)ᶜ ⊆ U := by
    intro x hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩
  refine ⟨(f '' Uᶜ)ᶜ, hAV, hopen, ?_⟩
  rw [Measure.map_apply hf.measurable hopen.measurableSet]
  exact (measure_mono hpre).trans_lt hmass

theorem regular_map_of_isProperMap [T2Space Y]
    (f : X → Y) (hf : IsProperMap f) (μ : Measure X) (hμ : μ.Regular) :
    (μ.map f).Regular := by
  letI : μ.Regular := hμ
  letI : (μ.map f).OuterRegular :=
    outerRegular_map_of_continuous_of_isClosedMap f hf.continuous hf.isClosedMap μ inferInstance
  letI : IsFiniteMeasureOnCompacts (μ.map f) := by
    constructor
    intro K hK
    rw [Measure.map_apply hf.continuous.measurable hK.measurableSet]
    exact (hf.isCompact_preimage hK).measure_lt_top
  exact ⟨(Measure.Regular.innerRegular (μ := μ)).map hf.continuous.measurable.aemeasurable
    (fun U hU => hU.preimage hf.continuous) (fun K hK => hK.image hf.continuous)
    (fun U hU => hU.measurableSet)⟩

end Preiss
