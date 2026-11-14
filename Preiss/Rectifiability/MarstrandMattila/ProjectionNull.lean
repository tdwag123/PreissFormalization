module

public import Preiss.Rectifiability.PurelyUnrectifiable
public import Preiss.Rectifiability.Cones
public import Preiss.Rectifiability.ProjectionEstimate
public import Preiss.Rectifiability.WeakApproximation.UniformTubes
public import Preiss.Rectifiability.MarstrandMattila.ProjectionCovering
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem ae_exists_outside_cone_of_purelyUnrectifiable
    (C : Set (Euclidean n)) (hp : PurelyUnrectifiable m C)
    (V : Plane m n) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᵐ a ∂((Measure.hausdorffMeasure (m : ℝ)).restrict C), ∀ r : ℝ, 0 < r →
      ∃ b ∈ C ∩ ball a r, b ∉ cone a V A := by
  classical
  let B (r : ℝ) : Set (Euclidean n) := {a | ∀ b ∈ C,
    r ≤ dist b a ∨ ‖(b - a) - proj V (b - a)‖ ≤ A * ‖proj V (b - a)‖}
  have hproj : Continuous (proj V) :=
    V.1.subtypeL.continuous.comp V.1.orthogonalProjectionOnto.continuous
  have hBclosed (r : ℝ) : IsClosed (B r) := by
    have hBeq : B r = ⋂ b ∈ C, {a : Euclidean n | r ≤ dist b a} ∪
        {a : Euclidean n | ‖(b - a) - proj V (b - a)‖ ≤ A * ‖proj V (b - a)‖} := by
      ext a
      simp only [B, Set.mem_ofPred_eq, mem_iInter, mem_union]
    rw [hBeq]
    apply isClosed_biInter
    intro b _
    have hpcont := hproj.comp (continuous_const.sub continuous_id :
      Continuous (fun a : Euclidean n ↦ b - a))
    exact (isClosed_le continuous_const (continuous_const.dist continuous_id)).union
      (isClosed_le ((continuous_const.sub continuous_id).sub hpcont).norm
        (continuous_const.mul hpcont.norm))
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Euclidean n)
  have : Countable D := hDc.to_subtype
  have hBnull (r : ℝ) (hr : 0 < r) :
      (Measure.hausdorffMeasure (m : ℝ)).restrict C (B r) = 0 := by
    let Z (q : D) := C ∩ B r ∩ ball q.val (r / 4)
    have hZ (q : D) : (Measure.hausdorffMeasure (m : ℝ)) (Z q) = 0 := by
      have hpair : ∀ x ∈ Z q, ∀ y ∈ Z q, y ∈ cone x V A := by
        intro x hx y hy
        have hxq : dist x q.val < r / 4 := hx.2
        have hyq : dist y q.val < r / 4 := hy.2
        have hyx : dist y x < r := by
          have ht := dist_triangle y q.val x
          rw [dist_comm q.val x] at ht
          linarith
        exact (hx.1.2 y hy.1.1).resolve_left (not_le.mpr hyx)
      obtain ⟨f, hf, hsub⟩ := exists_lipschitzGraph_of_pairwise_mem_cone V (Z q) hA hpair
      have hgraph : IsLipschitzGraph m (Set.range (graphMap V f)) := ⟨V, f, hf, rfl⟩
      have hrect := countablyRectifiable_subset_graph hgraph hsub
      have hsubC : Z q ⊆ C ∩ Z q := fun _ hz ↦ ⟨hz.1.1, hz⟩
      exact measure_mono_null hsubC (hp (Z q) hrect)
    rw [Measure.restrict_apply (hBclosed r).measurableSet]
    apply measure_mono_null (t := ⋃ q : D, Z q) ?_ (measure_iUnion_null hZ)
    rintro x ⟨hxB, hxC⟩
    obtain ⟨q, hq, hxq⟩ := hDd.exists_dist_lt x (show 0 < r / 4 by positivity)
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, ⟨hxC, hxB⟩, hxq⟩
  have hall : ∀ᵐ a ∂((Measure.hausdorffMeasure (m : ℝ)).restrict C),
      ∀ j : ℕ, a ∉ B (1 / (j + 1 : ℝ)) := by
    apply ae_all_iff.mpr
    intro j
    exact measure_eq_zero_iff_ae_notMem.mp (hBnull _ (by positivity))
  filter_upwards [hall] with a ha
  intro r hr
  by_contra hno
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hr
  apply ha j
  intro b hb
  by_cases hbr : dist b a < 1 / (j + 1 : ℝ)
  · right
    have hc : b ∈ cone a V A := by
      by_contra hnc
      exact hno ⟨b, ⟨hb, hbr.trans hj⟩, hnc⟩
    exact hc
  · exact Or.inl (le_of_not_gt hbr)


/-- Null projections on a purely unrectifiable piece with a fixed lower ball bound.
Compact tube approximation is applied at arbitrarily small apertures while preserving
the lower bound. The discarded sets are controlled by Lipschitz projection. -/
set_option maxHeartbeats 1500000 in
theorem measure_projection_eq_zero_of_uniformLower_and_weakApproximation
    (hm : 0 < m) (E C : Set (Euclidean n)) (hE : MeasurableSet E)
    (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) (hC : MeasurableSet C) (hCE : C ⊆ E)
    (hp : PurelyUnrectifiable m C)
    (hw : ∀ᵐ x ∂((Measure.hausdorffMeasure (m : ℝ)).restrict E).restrict C,
      MeasureWeaklyLinearlyApproximableAt m ((Measure.hausdorffMeasure (m : ℝ)).restrict E) x)
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀ : 0 < R₀)
    (hlower : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r < R₀ →
      ENNReal.ofReal (δ * r ^ m) ≤ (Measure.hausdorffMeasure (m : ℝ)).restrict E (ball x r)) :
    ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' C) = 0 := by
  classical
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (m : ℝ)
  let μ := H.restrict E
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfin.ne
  obtain ⟨K, hK, hcover⟩ := measure_projection_le_of_uniform_tubes_and_cone_escape m n hm
  intro V
  have hLip : LipschitzWith 1 (proj V) := V.1.lipschitzWith_starProjection
  have himage (S : Set (Euclidean n)) : H (proj V '' S) ≤ H S := by
    simpa only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] using
      hLip.hausdorffMeasure_image_le (d := (m : ℝ)) (by positivity) S
  have hsplit (A B : Set (Euclidean n)) :
      H (proj V '' A) ≤ H (proj V '' B) + H (proj V '' (A \ B)) := by
    have hsub : A ⊆ B ∪ (A \ B) := by
      intro x hx
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · exact Or.inr ⟨hx, hxB⟩
    have hh : H (proj V '' A) ≤ H (proj V '' (B ∪ (A \ B))) :=
      measure_mono (image_mono hsub)
    rw [image_union] at hh
    exact hh.trans (measure_union_le _ _)
  have hbound (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
      H (proj V '' C) ≤ ENNReal.ofReal ((K / δ) * e) * μ univ + ENNReal.ofReal e := by
    obtain ⟨D, hD, hDC, hsmall, R₁, hR₁, htube⟩ :=
      exists_compact_uniform_tubes_subset μ C hC hw hδ hR₀
        (show 0 < e / 100 by positivity) (show e / 100 ≤ 1 by linarith) he hlower
    let P : Euclidean n → Prop := fun a ↦ ∀ r : ℝ, 0 < r →
      ∃ b ∈ D ∩ ball a r, b ∉ cone a V (1 / e)
    let A : Set (Euclidean n) := {a | a ∈ D ∧ P a}
    have hAD : A ⊆ D := fun _ ha ↦ ha.1
    have hcone : ∀ᵐ a ∂H.restrict D, P a :=
      ae_exists_outside_cone_of_purelyUnrectifiable D (purelyUnrectifiable_mono hp hDC)
        V (by positivity)
    have hnull : H (D \ A) = 0 := by
      have hh : H {a | ¬(a ∈ D → P a)} = 0 :=
        ae_iff.mp ((ae_restrict_iff' hD.isClosed.measurableSet).mp hcone)
      apply measure_mono_null ?_ hh
      intro a ha hP
      exact ha.2 ⟨ha.1, hP ha.1⟩
    have himagenull : H (proj V '' (D \ A)) = 0 := le_antisymm
      ((himage (D \ A)).trans hnull.le) bot_le
    have hAproj : H (proj V '' A) ≤ ENNReal.ofReal ((K / δ) * e) * μ univ := by
      apply hcover μ D A V δ R₀ R₁ e hAD hδ hR₀ hR₁ he he1
      · intro a ha r hr hrR
        exact hlower a (hDC (hAD ha)) r hr hrR
      · intro a ha s hs hsR
        exact htube a (hAD ha) s hs hsR
      · exact fun a ha ↦ ha.2
    have hDproj : H (proj V '' D) ≤ ENNReal.ofReal ((K / δ) * e) * μ univ := by
      have hh := hsplit D A
      rw [himagenull, add_zero] at hh
      exact hh.trans hAproj
    have hHsmall : H (C \ D) < ENNReal.ofReal e := by
      have heq : μ (C \ D) = H (C \ D) := by
        rw [Measure.restrict_apply (hC.diff hD.isClosed.measurableSet)]
        rw [inter_eq_self_of_subset_left (sdiff_subset.trans hCE)]
      rwa [heq] at hsmall
    exact (hsplit C D).trans (add_le_add hDproj ((himage (C \ D)).trans hHsmall.le))
  apply le_antisymm ?_ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ξ hξ _
  simp only [ENNReal.bot_eq_zero, zero_add]
  change H (proj V '' C) ≤ (ξ : ℝ≥0∞)
  let A : ℝ := (K / δ) * (μ univ).toReal + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let e := min 1 ((ξ : ℝ) / A)
  have hξreal : 0 < (ξ : ℝ) := by exact_mod_cast hξ
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := min_le_left _ _
  have heξ : A * e ≤ (ξ : ℝ) := by
    have hh : e ≤ (ξ : ℝ) / A := min_le_right _ _
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hh
  have hmass : μ univ = ENNReal.ofReal (μ univ).toReal :=
    (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
  have heq : ENNReal.ofReal ((K / δ) * e) * μ univ + ENNReal.ofReal e = ENNReal.ofReal (A * e) := by
    rw [hmass, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) he.le]
    congr 1
    dsimp [A]
    ring
  have hh := hbound e he he1
  rw [heq] at hh
  apply hh.trans
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal heξ

/-- Exhaustion by closed approximation good sets reduces projection nullness to
pieces with a fixed positive lower mass bound. -/
theorem measure_projection_eq_zero_of_purelyUnrectifiable_weakApproximation
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞) (hp : PurelyUnrectifiable m E)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x) :
    ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' E) = 0 := by
  classical
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (m : ℝ)
  let μ := H.restrict E
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfin.ne
  let q : ℕ → ℝ := fun N ↦ 1 / (N + 1 : ℝ)
  have hq (N : ℕ) : 0 < q N := by dsimp [q]; positivity
  let C : ℕ → Set (Euclidean n) := fun N ↦ E ∩ weakApproximationGoodSet m μ 1 (q N) (q N)
  have hCm (N : ℕ) : MeasurableSet (C N) := hE.inter
    (isClosed_weakApproximationGoodSet μ zero_lt_one (hq N) (hq N)).measurableSet
  have hCE (N : ℕ) : C N ⊆ E := inter_subset_left
  have hprojC (N : ℕ) : ∀ V : Plane m n, H (proj V '' C N) = 0 := by
    apply measure_projection_eq_zero_of_uniformLower_and_weakApproximation hm E (C N) hE hfin
      (hCm N) (hCE N) (purelyUnrectifiable_mono hp (hCE N))
      (ae_restrict_of_ae hw) (show 0 < q N / 2 ^ m by positivity) (hq N)
    intro a ha r hr hrR
    obtain ⟨W, _, hlower⟩ := ha.2 (r / 2) (by positivity) (by linarith)
    have hh := hlower a (by simp) (mem_ball_self (by positivity : 0 < r / 2))
    have hμ := hh.trans (measure_mono (closedBall_subset_ball (show 1 * (r / 2) < r by linarith)))
    convert hμ using 1 <;> simp only [one_mul, div_pow] <;> congr 1 <;> ring
  have hcover : ∀ᵐ x ∂μ, x ∈ ⋃ N, C N := by
    filter_upwards [ae_restrict_mem hE, hw] with x hxE hx
    obtain ⟨N, hN⟩ := (weaklyLinearlyApproximableAt_iff_goodSet_exhaustion μ x).mp hx 1 zero_lt_one
    exact mem_iUnion.mpr ⟨N, hxE, hN⟩
  have hnull : H (E \ ⋃ N, C N) = 0 := by
    have hμnull : μ (E \ ⋃ N, C N) = 0 :=
      measure_mono_null (sdiff_subset_compl _ _) (ae_iff.mp hcover)
    have heq : μ (E \ ⋃ N, C N) = H (E \ ⋃ N, C N) := by
      rw [Measure.restrict_apply (hE.diff (MeasurableSet.iUnion hCm)),
        inter_eq_self_of_subset_left sdiff_subset]
    rwa [heq] at hμnull
  intro V
  have hLip : LipschitzWith 1 (proj V) := V.1.lipschitzWith_starProjection
  have hprojnull : H (proj V '' (E \ ⋃ N, C N)) = 0 := by
    apply le_antisymm ?_ zero_le
    have hh := hLip.hausdorffMeasure_image_le (d := (m : ℝ)) (by positivity) (E \ ⋃ N, C N)
    change H (proj V '' (E \ ⋃ N, C N)) ≤ (1 : ℝ≥0∞) ^ (m : ℝ) * H (E \ ⋃ N, C N) at hh
    simpa only [hnull, mul_zero] using hh
  have hprojUnion : H (proj V '' ⋃ N, C N) = 0 := by
    rw [image_iUnion]
    exact measure_iUnion_null fun N ↦ hprojC N V
  have hsub : E ⊆ (⋃ N, C N) ∪ (E \ ⋃ N, C N) := by
    intro x hx
    by_cases hxC : x ∈ ⋃ N, C N
    · exact Or.inl hxC
    · exact Or.inr ⟨hx, hxC⟩
  apply le_antisymm ?_ zero_le
  have hh : H (proj V '' E) ≤ H (proj V '' ((⋃ N, C N) ∪ (E \ ⋃ N, C N))) :=
    measure_mono (image_mono hsub)
  rw [image_union] at hh
  exact hh.trans ((measure_union_le _ _).trans (by rw [hprojUnion, hprojnull, add_zero]))

end Preiss
