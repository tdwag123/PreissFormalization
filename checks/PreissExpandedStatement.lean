import Preiss.Main
import Preiss.Geometry.LipschitzExtension

/-! Audit certificate: state the density and countable Lipschitz coverage
without using the project's density or rectifiability predicates. -/
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace PreissAudit
variable {m n : ℕ}

theorem preiss_expanded_statement
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ,
      0 < liminf (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal ((2*r)^m)) (𝓝[>] 0) ∧
      liminf (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal ((2*r)^m)) (𝓝[>] 0) =
        limsup (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal ((2*r)^m)) (𝓝[>] 0) ∧
      limsup (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal ((2*r)^m)) (𝓝[>] 0) < ∞) :
    μ ≪ (Measure.hausdorffMeasure (m : ℝ)) ∧
      ∃ F : Set (EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)),
        F.Countable ∧ (∀ f ∈ F, ∃ K : ℝ≥0, LipschitzWith K f) ∧
        μ (⋃ f ∈ F, Set.range f)ᶜ = 0 := by
  classical
  have hd : ∀ᵐ x ∂μ, Preiss.HasPositiveFiniteDensityAt m μ x := by
    filter_upwards [h] with x hx
    have heq : dimensional_density_ratio μ.toOuterMeasure (m : ℝ) x =ᶠ[𝓝[>] 0]
        (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal ((2*r)^m)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [dimensional_density_ratio_closedBall μ.toOuterMeasure (m : ℝ) x hr.le,
        Real.rpow_natCast]
      rfl
    unfold Preiss.HasPositiveFiniteDensityAt dimensional_lower_density dimensional_upper_density
    rw [liminf_congr heq, limsup_congr heq]
    exact hx
  obtain ⟨habs, s, ⟨t, ⟨P, hPc, hcover⟩, hnull⟩, hsc⟩ := Preiss.preiss μ hd
  haveI : Countable P := hPc.to_subtype
  have hext (p : P) : ∃ g : Preiss.Euclidean m → Preiss.Euclidean n,
      (∃ K : ℝ≥0, LipschitzWith K g) ∧ ∀ x : p.val.domain, g x = p.val.toFun x := by
    obtain ⟨K, hK⟩ := p.val.lipschitz
    exact Preiss.exists_lipschitz_extension_finiteDimensional p.val.domain p.val.toFun hK
  choose g hg he using hext
  let F := Set.range g
  have ht : t ⊆ ⋃ f ∈ F, Set.range f := by
    intro x hx
    obtain ⟨p, hp, v, hv⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨g ⟨p,hp⟩, ⟨⟨p,hp⟩,rfl⟩,
      ⟨v.val, (he ⟨p,hp⟩ v).trans hv⟩⟩
  refine ⟨habs, F, Set.countable_range g, ?_, ?_⟩
  · rintro f ⟨p,rfl⟩
    exact hg p
  · apply measure_mono_null (t := sᶜ ∪ (s \ t)) ?_ (measure_union_null hsc (habs hnull))
    intro x hx
    by_cases hxs : x ∈ s
    · exact Or.inr ⟨hxs, fun hxt => hx (ht hxt)⟩
    · exact Or.inl hxs

end PreissAudit
#print axioms PreissAudit.preiss_expanded_statement
