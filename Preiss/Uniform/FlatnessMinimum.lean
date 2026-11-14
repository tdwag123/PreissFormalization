module

public import Preiss.Uniform.Flatness
public import Preiss.Geometry.PlaneTopology
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.FunProp

/-! # Existence of a plane minimizing quadratic distance energy

Only finiteness on compact sets is needed. The cutoff need not be nonnegative.
-/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem flatnessEnergy_eq_integral_projection (φ : C_c(Euclidean n, ℝ))
    (μ : Measure (Euclidean n)) (V : Plane m n) :
    flatnessEnergy φ μ V = ∫ z, φ z * ‖z - planeProjection V z‖ ^ 2 ∂μ := by
  have h (z : Euclidean n) : infDist z (V.1 : Set (Euclidean n)) =
      ‖z - V.1.starProjection z‖ := by
    rw [Submodule.starProjection_minimal, infDist_eq_iInf]
    rfl
  unfold flatnessEnergy planeProjection
  apply integral_congr_ae
  filter_upwards [] with z
  rw [h]

theorem continuous_integral_projectionEnergy (φ : C_c(Euclidean n, ℝ))
    (μ : Measure (Euclidean n)) [IsFiniteMeasureOnCompacts μ] :
    Continuous (fun P : Euclidean n →L[ℝ] Euclidean n =>
      ∫ z, φ z * ‖z - P z‖ ^ 2 ∂μ) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := tsupport φ) φ.hasCompactSupport
  · fun_prop
  · intro P z _ hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem flatness_exists_minimizer_of_finite_on_compacts (hmn : m ≤ n)
    (φ : C_c(Euclidean n, ℝ)) (μ : Measure (Euclidean n))
    [IsFiniteMeasureOnCompacts μ] :
    ∃ V : Plane m n, flatness m φ μ = flatnessEnergy φ μ V ∧
      ∀ W : Plane m n, flatness m φ μ ≤ flatnessEnergy φ μ W := by
  obtain ⟨V₀⟩ := nonempty_plane_of_le hmn
  have hne : (rankProjectionSet m n).Nonempty := by
    rw [← range_planeProjection]
    exact ⟨planeProjection V₀, Set.mem_range_self V₀⟩
  obtain ⟨P, hP, hmin⟩ := (isCompact_rankProjectionSet m n).exists_isMinOn hne
    (continuous_integral_projectionEnergy φ μ).continuousOn
  rw [← range_planeProjection] at hP
  obtain ⟨V, rfl⟩ := hP
  have hV (W : Plane m n) : flatnessEnergy φ μ V ≤ flatnessEnergy φ μ W := by
    rw [flatnessEnergy_eq_integral_projection, flatnessEnergy_eq_integral_projection]
    exact hmin (by rw [← range_planeProjection]; exact Set.mem_range_self W)
  have heq : flatness m φ μ = flatnessEnergy φ μ V := by
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_range_self V, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact hV W
  refine ⟨V, heq, ?_⟩
  intro W
  rw [heq]
  exact hV W

end Preiss
