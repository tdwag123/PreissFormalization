import Preiss.Uniform.FlatnessContinuity
import Preiss.Tangent.Blowup
import Preiss.Tangent.BlowupSupport
import Preiss.Tangent.Continuity

open MeasureTheory Set Filter Topology
open scoped CompactlySupported
namespace Preiss
variable {n m : ℕ}

theorem continuousOn_flatness_dimensionalBlowup (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (hφ : IsFlatnessCutoff φ)
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (x : Euclidean n) :
    ContinuousOn (fun r => flatness m φ (dimensionalBlowup m μ x r)) (Ioi 0) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_iff_seqContinuous.mpr
  intro r s hrs
  have hrs' : Tendsto (fun i => (r i : ℝ)) atTop (𝓝 (s : ℝ)) :=
    (continuous_subtype_val.tendsto s).comp hrs
  have hblow := vague_dimensionalBlowup_moving (m := m) (fun _ => μ) μ
    (fun _ => hμ) hμ (fun _ => tendsto_const_nhds) (fun _ => x) x tendsto_const_nhds
    (fun i => (r i : ℝ)) (s : ℝ) (fun i => (r i).property) s.property hrs'
  change Tendsto (fun i => flatness m φ (dimensionalBlowup m μ x (r i : ℝ)))
    atTop (𝓝 (flatness m φ (dimensionalBlowup m μ x (s : ℝ))))
  exact flatness_tendsto_of_vague hmn φ _ _
    (fun i => regular_dimensionalBlowup μ hμ x (r i).property)
    (regular_dimensionalBlowup μ hμ x s.property) hblow

end Preiss
