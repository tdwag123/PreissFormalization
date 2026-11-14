import Preiss.Uniform.DimensionReduction
import Preiss.Uniform.Classification

/-! # Flat pseudotangents of uniform measures

The radii remain at most one, as required by the support-centered recentering argument.
-/

open MeasureTheory Metric Set Filter Topology
namespace Preiss
variable {m n : ℕ}

theorem unitUniform_exists_flat_uniformPseudotangent (hm : 0 < m) (hmn : m ≤ n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ V : Plane m n, IsUniformPseudotangent m ν (unitFlat V) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases heq : m = n
    · subst n
      let V : Plane m m := ⟨⊤, by simp [finrank_euclideanSpace_fin]⟩
      have hflat : ν = unitFlat V :=
        unitUniform_eq_flat_of_support_subset_plane hm ν hν V (fun _ _ => trivial)
      refine ⟨V, regular_unitFlat V, fun _ => 0, fun _ => 1,
        fun _ => hν.2.1, fun _ => ⟨zero_lt_one, le_rfl⟩, ?_⟩
      simpa only [dimensionalBlowup, one_pow, ENNReal.ofReal_one, inv_one, smul_zero,
        sub_zero, one_smul, Measure.map_id'] using
        (show Measure.WeaklyConverges (fun _ : ℕ => ν) (unitFlat V) from
          fun f => hflat ▸ tendsto_const_nhds)
    · have hlt : m < n := lt_of_le_of_ne hmn heq
      obtain ⟨L, ξ, hξ, horbit⟩ := uniform_dimension_reduction hm hlt ν hν
      obtain ⟨V, hV⟩ := ih (n - 1) (by omega) (by omega) ξ hξ
      let f : V.1 →ₗ[ℝ] Euclidean n := L.toLinearMap.comp V.1.subtype
      have hf : Function.Injective f := L.injective.comp Subtype.val_injective
      let W : Plane m n := ⟨f.range, by rw [LinearMap.finrank_range_of_inj hf, V.property]⟩
      have hmapunit : IsUnitUniform m ((unitFlat V).map L) :=
        isUnitUniform_map_linearIsometry L (unitFlat V) (isUnitUniform_unitFlat V)
      have hsupp : ((unitFlat V).map L).support ⊆ (W.1 : Set (Euclidean n)) := by
        rw [measure_support_map_of_continuous_of_isClosedMap L L.continuous
          L.isometry.isClosedEmbedding.isClosedMap (unitFlat V) (regular_unitFlat V),
          unitFlat_support]
        rintro z ⟨v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
      have hflat := unitUniform_eq_flat_of_support_subset_plane hm _ hmapunit W hsupp
      refine ⟨W, ?_⟩
      rw [← hflat]
      exact uniformPseudotangent_trans ν (ξ.map L) ((unitFlat V).map L) hν horbit
        (uniformPseudotangent_map_linearIsometry L ξ (unitFlat V) hξ hV)

theorem uniform_has_flat_pseudotangent (hm : 0 < m) (hmn : m ≤ n)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν) :
    ∃ (V : Plane m n) (a : ℕ → Euclidean n) (r : ℕ → ℝ),
      (∀ i, a i ∈ ν.support) ∧ (∀ i, 0 < r i ∧ r i ≤ 1) ∧
      Measure.WeaklyConverges (fun i ↦ dimensionalBlowup m ν (a i) (r i)) (unitFlat V) := by
  obtain ⟨V, _, a, r, ha, hr, hlim⟩ := unitUniform_exists_flat_uniformPseudotangent hm hmn ν hν
  exact ⟨V, a, r, ha, hr, hlim⟩

end Preiss
