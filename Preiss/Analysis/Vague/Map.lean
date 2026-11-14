import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import FormalizingGMT.WeakConvergence.Basic

/-! # Vague convergence under cocompact maps -/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported
namespace Preiss
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem weaklyConverges_map_cocompact (f : CocompactMap X Y)
    (μ : ℕ → Measure X) (ν : Measure X) (h : Measure.WeaklyConverges μ ν) :
    Measure.WeaklyConverges (fun i => (μ i).map f) (ν.map f) := by
  intro g
  have hmap (ρ : Measure X) : (∫ y, g y ∂ρ.map f) = ∫ x, (g.comp f) x ∂ρ :=
    integral_map f.continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable
  simpa only [hmap] using h (g.comp f)

theorem weaklyConverges_map_of_isProperMap (f : X → Y) (hf : IsProperMap f)
    (μ : ℕ → Measure X) (ν : Measure X) (h : Measure.WeaklyConverges μ ν) :
    Measure.WeaklyConverges (fun i => (μ i).map f) (ν.map f) := by
  let f' : CocompactMap X Y := ⟨⟨f, hf.continuous⟩,
    CocompactMap.tendsto_of_forall_preimage (fun K hK => hf.isCompact_preimage hK)⟩
  exact weaklyConverges_map_cocompact f' μ ν h

end Preiss
