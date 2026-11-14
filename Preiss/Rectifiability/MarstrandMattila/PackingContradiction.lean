import Preiss.Rectifiability.MarstrandMattila.PackingCore
import Preiss.Rectifiability.MarstrandMattila.CompactSelection

/-! # The Hausdorff-measure packing contradiction -/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem false_of_null_projections_and_uniform_weakApproximation
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hpos : 0 < (Measure.hausdorffMeasure (m : ℝ)) E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞)
    (hu : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), UpperPowerBoundAt m (((Measure.hausdorffMeasure (m : ℝ))).restrict E) x)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x)
    (hproj : ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' E) = 0) : False := by
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (m : ℝ)
  let μ := H.restrict E
  obtain ⟨C, hC, hpoint⟩ := exists_upper_mass_small_sdiff_point m n
  obtain ⟨F, δ, R₀, hF, hFE, hFpos, hδ, hR₀, hlower, hselect⟩ :=
    exists_nested_compact_twoSided_approximation E hE hpos hfin hu hw
  apply false_of_compact_twoSided_approximation hm μ F hδ hR₀ hC hlower ?_ ?_
  · intro η hη hη1
    obtain ⟨G, γ, R, hG, hGF, hGpos, hγ, hR, hRR₀, happ⟩ := hselect η hη hη1
    refine ⟨G, γ, R, hG, hGF, hγ, hR, hRR₀, happ, ?_⟩
    intro t ht
    obtain ⟨a, R', ha, hR', hbound⟩ := hpoint E G hE hG.isClosed.measurableSet
      (hGF.trans hFE) hfin hGpos t ht
    refine ⟨a, R', ha, hR', ?_⟩
    intro r hr hrR'
    refine ⟨(hbound r hr hrR').1, ?_⟩
    dsimp only [μ]
    rw [Measure.restrict_apply (isOpen_ball.measurableSet.diff hG.isClosed.measurableSet)]
    have heq : (ball a (2 * r) \ G) ∩ E = (E \ G) ∩ ball a (2 * r) := by
      ext x
      simp only [mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [heq]
    exact (hbound r hr hrR').2
  · intro V
    exact measure_mono_null (image_mono hFE) (hproj V)


end Preiss
