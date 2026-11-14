import Preiss.Uniform.FlatnessMinimum
import Preiss.Analysis.SequentialLimits
import Preiss.Analysis.Vague.ProjectionEnergy
import Mathlib.Topology.Sequences

/-! # Vague continuity of minimum distance energy

Compactly supported continuous cutoffs may have either sign. -/

open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem flatness_tendsto_of_vague (hmn : m ≤ n) (φ : C_c(Euclidean n, ℝ))
    (μ : ℕ → Measure (Euclidean n)) (ν : Measure (Euclidean n))
    (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν) :
    Tendsto (fun i => flatness m φ (μ i)) atTop (𝓝 (flatness m φ ν)) := by
  have hex (i : ℕ) : ∃ V : Plane m n,
      flatness m φ (μ i) = flatnessEnergy φ (μ i) V ∧
        ∀ W : Plane m n, flatness m φ (μ i) ≤ flatnessEnergy φ (μ i) W := by
    letI : (μ i).Regular := hμ i
    exact flatness_exists_minimizer_of_finite_on_compacts hmn φ (μ i)
  choose V heq hmin using hex
  letI : ν.Regular := hν
  obtain ⟨V₀, hνeq, hνmin⟩ := flatness_exists_minimizer_of_finite_on_compacts hmn φ ν
  apply tendsto_of_subsequence_subsequence
  intro ψ hψ
  obtain ⟨Q, hQ, ρ, hρ, hPQ⟩ := (isCompact_rankProjectionSet m n).tendsto_subseq
    (x := fun i => planeProjection (V (ψ i))) (fun i => by
      rw [← range_planeProjection]
      exact Set.mem_range_self _)
  rw [← range_planeProjection] at hQ
  obtain ⟨W, rfl⟩ := hQ
  have hsub : Measure.WeaklyConverges (fun i => μ (ψ (ρ i))) ν :=
    fun f => (hlim f).comp (hψ.comp hρ).tendsto_atTop
  have henergy : Tendsto (fun i => flatnessEnergy φ (μ (ψ (ρ i))) (V (ψ (ρ i))))
      atTop (𝓝 (flatnessEnergy φ ν W)) := by
    simpa only [flatnessEnergy_eq_integral_projection, Function.comp_def] using
      vague_integral_projectionEnergy_moving φ (fun i => μ (ψ (ρ i))) ν
        (fun i => hμ _) hν hsub (fun i => planeProjection (V (ψ (ρ i))))
        (planeProjection W) hPQ
  have hfixed : Tendsto (fun i => flatnessEnergy φ (μ (ψ (ρ i))) V₀)
      atTop (𝓝 (flatnessEnergy φ ν V₀)) := by
    simpa only [flatnessEnergy_eq_integral_projection] using
      vague_integral_projectionEnergy_moving φ (fun i => μ (ψ (ρ i))) ν
        (fun i => hμ _) hν hsub (fun _ => planeProjection V₀) (planeProjection V₀)
        tendsto_const_nhds
  have hupper : flatnessEnergy φ ν W ≤ flatnessEnergy φ ν V₀ :=
    le_of_tendsto_of_tendsto henergy hfixed (Filter.Eventually.of_forall fun i =>
      (heq _).symm.le.trans (hmin _ V₀))
  have hE : flatnessEnergy φ ν W = flatness m φ ν := by
    apply le_antisymm ?_ (hνmin W)
    exact hupper.trans_eq hνeq.symm
  refine ⟨ρ, hρ, ?_⟩
  change Tendsto (fun i => flatness m φ (μ (ψ (ρ i)))) atTop (𝓝 (flatness m φ ν))
  have hseq : (fun i => flatness m φ (μ (ψ (ρ i)))) =
      (fun i => flatnessEnergy φ (μ (ψ (ρ i))) (V (ψ (ρ i)))) :=
    funext fun i => heq _
  rw [hseq]
  rwa [hE] at henergy

end Preiss
