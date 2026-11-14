import Preiss.Uniform.Scaling
import Preiss.Tangent.Continuity
import Preiss.Analysis.Vague.Metrization
import FormalizingGMT.WeakConvergence.CompactnessCriterion
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences

/-! # Closedness and compactness of uniform measure families -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
namespace Preiss
variable {m n : ℕ}

/-- S05a: regularity of the proposed limit is explicit. -/
theorem isUnitUniform_of_vague (ν : ℕ → Measure (Euclidean n))
    (hν : ∀ i, IsUnitUniform m (ν i)) (ξ : Measure (Euclidean n))
    (hξ : ξ.Regular) (hlim : Measure.WeaklyConverges ν ξ) :
    IsUnitUniform m ξ := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds ν ξ
    (fun i => (hν i).1) hξ).mp hlim
  have pass (x : Euclidean n)
      (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
        ∃ y ∈ (ν i).support, dist y x < ε) :
      ∀ r : ℝ, 0 < r → ξ (closedBall x r) = ENNReal.ofReal (r ^ m) := by
    intro r hr
    apply le_antisymm
    · have key : ∀ v : ℝ, r < v → ξ (closedBall x r) ≤ ENNReal.ofReal (v ^ m) := by
        intro v hv
        let u := (r + v) / 2
        have hru : r < u := by dsimp [u]; linarith
        have huv : u < v := by dsimp [u]; linarith
        have hvpos : 0 < v := hr.trans hv
        have hevent : ∀ᶠ i in atTop,
            ν i (ball x u) ≤ ENNReal.ofReal (v ^ m) := by
          filter_upwards [hnear (v - u) (sub_pos.mpr huv)] with i hi
          obtain ⟨y, hy, hdist⟩ := hi
          have hsub : ball x u ⊆ closedBall y v := by
            intro z hz
            have hz' : dist z x < u := hz
            have hxy : dist x y < v - u := by rwa [dist_comm]
            have htri := dist_triangle z x y
            change dist z y ≤ v
            linarith
          calc ν i (ball x u) ≤ ν i (closedBall y v) := measure_mono hsub
            _ = ENNReal.ofReal (v ^ m) := (hν i).2.2 y hy v hvpos
        calc ξ (closedBall x r) ≤ ξ (ball x u) :=
            measure_mono (closedBall_subset_ball hru)
          _ ≤ liminf (fun i => ν i (ball x u)) atTop := hb.2 _ isOpen_ball
          _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (v ^ m)) atTop :=
            liminf_le_liminf hevent
          _ = ENNReal.ofReal (v ^ m) := liminf_const _
      have hcont : Tendsto (fun v : ℝ => ENNReal.ofReal (v ^ m)) (𝓝[>] r)
          (𝓝 (ENNReal.ofReal (r ^ m))) :=
        ((ENNReal.continuous_ofReal.comp (continuous_pow m)).tendsto r).mono_left
          nhdsWithin_le_nhds
      exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)
    · have key : ∀ w : ℝ, 0 < w → w < r →
          ENNReal.ofReal (w ^ m) ≤ ξ (closedBall x r) := by
        intro w hw hwr
        have hevent : ∀ᶠ i in atTop,
            ENNReal.ofReal (w ^ m) ≤ ν i (closedBall x r) := by
          filter_upwards [hnear (r - w) (sub_pos.mpr hwr)] with i hi
          obtain ⟨y, hy, hdist⟩ := hi
          have hsub : closedBall y w ⊆ closedBall x r := by
            intro z hz
            have hz' : dist z y ≤ w := hz
            have htri := dist_triangle z y x
            change dist z x ≤ r
            linarith
          calc ENNReal.ofReal (w ^ m) = ν i (closedBall y w) :=
              ((hν i).2.2 y hy w hw).symm
            _ ≤ ν i (closedBall x r) := measure_mono hsub
        calc ENNReal.ofReal (w ^ m) =
              liminf (fun _ : ℕ => ENNReal.ofReal (w ^ m)) atTop := (liminf_const _).symm
          _ ≤ liminf (fun i => ν i (closedBall x r)) atTop := liminf_le_liminf hevent
          _ ≤ limsup (fun i => ν i (closedBall x r)) atTop := liminf_le_limsup
          _ ≤ ξ (closedBall x r) := hb.1 _ (isCompact_closedBall _ _)
      have hcont : Tendsto (fun w : ℝ => ENNReal.ofReal (w ^ m)) (𝓝[<] r)
          (𝓝 (ENNReal.ofReal (r ^ m))) :=
        ((ENNReal.continuous_ofReal.comp (continuous_pow m)).tendsto r).mono_left
          nhdsWithin_le_nhds
      refine le_of_tendsto hcont ?_
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds hr)] with w hw1 hw2
      exact key w hw2 hw1
  have hzero := pass 0 (fun ε hε => Eventually.of_forall
    (fun i => ⟨0, (hν i).2.1, by simpa using hε⟩))
  have hsupport : (0 : Euclidean n) ∈ ξ.support := by
    apply Metric.nhds_basis_ball.mem_measureSupport.mpr
    intro r hr
    have hmass : 0 < ξ (closedBall 0 (r / 2)) := by
      rw [hzero (r / 2) (half_pos hr)]
      exact ENNReal.ofReal_pos.mpr (pow_pos (half_pos hr) m)
    exact hmass.trans_le (measure_mono (closedBall_subset_ball (half_lt_self hr)))
  refine ⟨hξ, hsupport, ?_⟩
  intro x hx
  apply pass x
  intro ε hε
  have hpos : 0 < ξ (ball x ε) :=
    (Measure.mem_support_iff_forall x).mp hx _ (ball_mem_nhds x hε)
  have hevent : ∀ᶠ i in atTop, 0 < ν i (ball x ε) :=
    eventually_lt_of_lt_liminf (hpos.trans_le (hb.2 _ isOpen_ball))
  filter_upwards [hevent] with i hi
  obtain ⟨y, hyball, hysupport⟩ := Measure.nonempty_inter_support_of_pos hi
  exact ⟨y, hysupport, hyball⟩

/-- S05b: strict monotonicity keeps the selected sequence a genuine subsequence. -/
theorem exists_vague_subsequence_unitUniform (ν : ℕ → Measure (Euclidean n))
    (hν : ∀ i, IsUnitUniform m (ν i)) :
    ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧ IsUnitUniform m ξ ∧
      Measure.WeaklyConverges (fun i ↦ ν (φ i)) ξ := by
  have hbound : ∀ K : Set (Euclidean n), IsCompact K →
      ∃ C : ℝ≥0, ∀ i, ν i K ≤ C := by
    intro K hK
    obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Euclidean n)
    refine ⟨(R ^ m).toNNReal, fun i => ?_⟩
    calc ν i K ≤ ν i (closedBall 0 R) := measure_mono hKR
      _ = ENNReal.ofReal (R ^ m) := (hν i).2.2 0 (hν i).2.1 R hR
      _ = ((R ^ m).toNNReal : ℝ≥0∞) := rfl
  obtain ⟨φ, ξ, hφ, hξ, hlim⟩ :=
    exists_vaguelyConvergent_subseq_of_compact_bounded ν hbound
  exact ⟨φ, ξ, hφ, isUnitUniform_of_vague _ (fun i => hν (φ i)) ξ hξ hlim, hlim⟩

/-- S05c: support nonemptiness is part of the ball-law predicate. -/
theorem exists_vague_subsequence_uniform_of_dist_support_tendsto_zero
    (ν : ℕ → Measure (Euclidean n))
    (hν : ∀ i, IsUniformWithConstant m 1 (ν i))
    (hnear : Tendsto (fun i ↦ infDist (0 : Euclidean n) (ν i).support) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧ IsUnitUniform m ξ ∧
      Measure.WeaklyConverges (fun i ↦ ν (φ i)) ξ := by
  classical
  choose y hy hdist using fun i =>
    (Measure.isClosed_support (μ := ν i)).exists_infDist_eq_dist (hν i).2.1
      (0 : Euclidean n)
  have hy0 : Tendsto y atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have heq : (fun i => dist (y i) 0) =
        (fun i => infDist (0 : Euclidean n) (ν i).support) := by
      funext i
      rw [dist_comm, ← hdist i]
    rw [heq]
    exact hnear
  let τ (i : ℕ) := dimensionalBlowup m (ν i) (y i) 1
  have hτ (i : ℕ) : IsUnitUniform m (τ i) := by
    apply (isUnitUniform_iff_constant_one _).mpr
    refine ⟨uniformWithConstant_dimensionalBlowup (ν i) (hν i) (y i) zero_lt_one, ?_⟩
    change (0 : Euclidean n) ∈ (dimensionalBlowup m (ν i) (y i) 1).support
    rw [dimensionalBlowup_support (ν i) (y i) zero_lt_one]
    exact ⟨y i, hy i, by simp⟩
  obtain ⟨φ, ξ, hφ, hξ, hlim⟩ := exists_vague_subsequence_unitUniform τ hτ
  have hneg : Tendsto (fun i => -y (φ i)) atTop (𝓝 (0 : Euclidean n)) := by
    simpa using (hy0.comp hφ.tendsto_atTop).neg
  have hundo (i : ℕ) : dimensionalBlowup m (τ i) (-y i) 1 = ν i := by
    dsimp only [τ]
    rw [dimensionalBlowup_comp (ν i) (y i) (-y i) 1 1 zero_lt_one zero_lt_one]
    simp [dimensionalBlowup]
  have hconv := vague_dimensionalBlowup_moving (m := m)
    (fun i => τ (φ i)) ξ (fun i => (hτ (φ i)).1) hξ.1 hlim
    (fun i => -y (φ i)) 0 hneg (fun _ => 1) 1 (fun _ => zero_lt_one)
    zero_lt_one tendsto_const_nhds
  have hid : dimensionalBlowup m ξ 0 1 = ξ := by simp [dimensionalBlowup]
  simp only [hundo, hid] at hconv
  exact ⟨φ, ξ, hφ, hξ, hconv⟩

/-- S06c: all ball constants in one fixed positive compact interval are allowed. -/
theorem unitUniform_totallyBounded (M : VagueMetrization n)
    {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    letI := M.metric
    TotallyBounded {ν : RegularEuclideanMeasure n | ∃ q ∈ Icc c C,
      IsUniformWithConstant m q ν.1 ∧ (0 : Euclidean n) ∈ ν.1.support} := by
  classical
  letI := M.metric
  apply IsSeqCompact.totallyBounded
  intro μ hμ
  choose q hq hμq hμ0 using hμ
  have hqpos (i : ℕ) : 0 < q i := hc.trans_le (hq i).1
  let τ (i : ℕ) := ENNReal.ofReal ((q i)⁻¹) • (μ i).val
  have hτ (i : ℕ) : IsUnitUniform m (τ i) := by
    apply (isUnitUniform_iff_constant_one _).mpr
    constructor
    · have h := uniformWithConstant_smul (μ i).val (hμq i) (inv_pos.mpr (hqpos i))
      simpa only [inv_mul_cancel₀ (hqpos i).ne'] using h
    · change (0 : Euclidean n) ∈
        (ENNReal.ofReal ((q i)⁻¹) • (μ i).val).support
      rw [measure_support_smul _ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hqpos i))).ne']
      exact hμ0 i
  obtain ⟨q₀, hq₀, ψ, hψ, hqconv⟩ := isCompact_Icc.tendsto_subseq hq
  obtain ⟨φ, ξ, hφ, hξ, hlim⟩ :=
    exists_vague_subsequence_unitUniform (fun i => τ (ψ i)) (fun i => hτ (ψ i))
  have hq₀pos : 0 < q₀ := hc.trans_le hq₀.1
  let η := ENNReal.ofReal q₀ • ξ
  have hηq : IsUniformWithConstant m q₀ η := by
    have h := uniformWithConstant_smul ξ
      ((isUnitUniform_iff_constant_one ξ).mp hξ).1 hq₀pos
    simpa only [mul_one] using h
  have hη0 : (0 : Euclidean n) ∈ η.support := by
    dsimp only [η]
    rw [measure_support_smul _ (ENNReal.ofReal_pos.mpr hq₀pos).ne']
    exact hξ.2.1
  have hundo (i : ℕ) : ENNReal.ofReal (q i) • τ i = (μ i).val := by
    dsimp only [τ]
    rw [smul_smul, ← ENNReal.ofReal_mul (hqpos i).le,
      mul_inv_cancel₀ (hqpos i).ne', ENNReal.ofReal_one, one_smul]
  have hqsub : Tendsto (fun i => q (ψ (φ i))) atTop (𝓝 q₀) :=
    hqconv.comp hφ.tendsto_atTop
  have hconv := vague_smul_map_sub_div (fun i => τ (ψ (φ i))) ξ
    (fun i => (hτ (ψ (φ i))).1) hξ.1 hlim
    (fun _ => 0) 0 tendsto_const_nhds (fun _ => 1) 1 (fun _ => zero_lt_one)
    zero_lt_one tendsto_const_nhds (fun i => q (ψ (φ i))) q₀
    (fun i => (hqpos (ψ (φ i))).le) hq₀pos.le hqsub
  have hconv' : Measure.WeaklyConverges (fun i => (μ (ψ (φ i))).val) η := by
    simpa only [inv_one, sub_zero, one_smul, Measure.map_id', hundo] using hconv
  refine ⟨⟨η, hηq.1⟩, ⟨q₀, hq₀, hηq, hη0⟩, ψ ∘ φ, hψ.comp hφ, ?_⟩
  exact (M.tendsto_iff (μ ∘ (ψ ∘ φ)) ⟨η, hηq.1⟩).mpr hconv'

end Preiss
