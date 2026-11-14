module

public import Preiss.Analysis.MovingSets
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.OrderClosed

/-! # Closed sets with uniform upper ball-mass bounds -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace Preiss

def ballPowerUpperBoundSet {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (m : ℕ) (μ : Measure X) (b R : ℝ) : Set X :=
  {x | ∀ r : ℝ, 0 < r → r < R → μ (ball x r) ≤ ENNReal.ofReal (b * r ^ m)}

theorem isClosed_ballPowerUpperBoundSet {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (m : ℕ) (μ : Measure X) (b R : ℝ) : IsClosed (ballPowerUpperBoundSet m μ b R) := by
  apply IsSeqClosed.isClosed
  intro x y hx hxy r hr hrR
  apply measure_le_of_pointwise_eventually_mem μ (fun i ↦ ball (x i) r)
  · exact Eventually.of_forall fun i ↦ hx i r hr hrR
  · intro z hz
    exact (tendsto_const_nhds.dist hxy).eventually_lt_const hz

theorem ballPowerUpperBoundSet_mono {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (m : ℕ) (μ : Measure X) {b b' R R' : ℝ} (hb : b ≤ b') (hR : R' ≤ R) :
    ballPowerUpperBoundSet m μ b R ⊆ ballPowerUpperBoundSet m μ b' R' := by
  intro x hx r hr hrR
  exact (hx r hr (hrR.trans_le hR)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hb (pow_nonneg hr.le m)))

end Preiss
