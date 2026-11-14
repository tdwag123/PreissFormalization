module

public import Preiss.Geometry.Cones
public import Preiss.Geometry.LipschitzExtension
public import Preiss.Rectifiability.Graphs

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem exists_lipschitzGraph_of_pairwise_mem_cone
    (V : Plane m n) (F : Set (Euclidean n)) {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ x ∈ F, ∀ y ∈ F, y ∈ cone x V a) :
    ∃ f : V.1 → ↥(V.1ᗮ), (∃ K : ℝ≥0, LipschitzWith K f) ∧
      F ⊆ Set.range (graphMap V f) := by
  classical
  let P := V.1.orthogonalProjectionOnto
  let Q := (V.1ᗮ).orthogonalProjectionOnto
  have hinj : Set.InjOn P F := by
    intro x hx y hy hxy
    have hc := hF x hx y hy
    change ‖(y - x) - proj V (y - x)‖ ≤ a * ‖proj V (y - x)‖ at hc
    have hp : proj V (y - x) = 0 := by
      change (P (y - x) : Euclidean n) = 0
      simp only [map_sub, hxy, sub_self, Submodule.coe_zero]
    simp only [hp, sub_zero, norm_zero, mul_zero] at hc
    exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hc (norm_nonneg _)))).symm
  let A : Set V.1 := P '' F
  let pick : A → Euclidean n := fun v ↦ Classical.choose v.property
  have hpick (v : A) : pick v ∈ F ∧ P (pick v) = (v : V.1) :=
    Classical.choose_spec v.property
  let g : A → ↥(V.1ᗮ) := fun v ↦ Q (pick v)
  have hg : LipschitzWith (Real.toNNReal a) g := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hc := hF (pick v) (hpick v).1 (pick u) (hpick u).1
    change ‖(pick u - pick v) - proj V (pick u - pick v)‖ ≤
      a * ‖proj V (pick u - pick v)‖ at hc
    have hq : dist (g u) (g v) =
        ‖(pick u - pick v) - proj V (pick u - pick v)‖ := by
      change dist (Q (pick u)) (Q (pick v)) = _
      rw [dist_eq_norm, ← map_sub]
      change ‖(Q (pick u - pick v) : Euclidean n)‖ = _
      simpa only [Q, proj, Submodule.starProjection_apply] using
        congrArg norm (V.1.starProjection_orthogonal_val (pick u - pick v))
    have hp : ‖proj V (pick u - pick v)‖ = dist u v := by
      change ‖P (pick u - pick v)‖ = dist (u : V.1) (v : V.1)
      rw [map_sub, (hpick u).2, (hpick v).2, dist_eq_norm]
    rw [hq, Real.coe_toNNReal a ha]
    exact hc.trans_eq (congrArg (fun b : ℝ ↦ a * b) hp)
  obtain ⟨f, hf, hext⟩ := exists_lipschitz_extension_finiteDimensional A g hg
  refine ⟨f, hf, ?_⟩
  intro z hz
  let v : A := ⟨P z, ⟨z, hz, rfl⟩⟩
  have hpz : pick v = z := hinj (hpick v).1 hz (hpick v).2
  have hfz : f (P z) = Q z := by
    have h := hext v
    change f (P z) = Q (pick v) at h
    rwa [hpz] at h
  refine ⟨P z, ?_⟩
  change (P z : Euclidean n) + (f (P z) : Euclidean n) = z
  rw [hfz]
  have hq : (Q z : Euclidean n) = z - (P z : Euclidean n) := by
    simpa only [P, Q, Submodule.starProjection_apply] using
      V.1.starProjection_orthogonal_val z
  rw [hq, add_comm, sub_add_cancel]

end Preiss
