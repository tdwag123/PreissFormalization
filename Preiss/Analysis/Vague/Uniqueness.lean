import FormalizingGMT.WeakConvergence.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! # Uniqueness of regular vague limits -/

open MeasureTheory Filter Topology
namespace Preiss

theorem vague_limit_unique
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) (ν ξ : Measure X)
    (hν : ν.Regular) (hξ : ξ.Regular)
    (hμν : Measure.WeaklyConverges μ ν) (hμξ : Measure.WeaklyConverges μ ξ) : ν = ξ := by
  letI : ν.Regular := hν
  letI : ξ.Regular := hξ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact tendsto_nhds_unique (hμν f) (hμξ f)

end Preiss
