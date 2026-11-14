import Preiss.Tangent.Extraction
import Preiss.Analysis.Vague.Metrization

/-! # Closure and subsequence compactness of tangent families -/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem dimensionalTangent_closed
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (ν : ℕ → Measure (Euclidean n)) (ξ : Measure (Euclidean n))
    (hν : ∀ i, IsDimensionalTangent m μ (ν i) x)
    (hlim : Measure.WeaklyConverges ν ξ) (hξ : ξ.Regular) (hξ0 : ξ ≠ 0) :
    IsDimensionalTangent m μ ξ x := by
  classical
  choose r hr hr0 hrow using fun i => (hν i).2.2
  let P (i j : ℕ) := r i j < 1 / ((i : ℝ) + 1)
  have hP (i : ℕ) : ∀ᶠ j in atTop, P i j :=
    (hr0 i).eventually_lt_const (by positivity)
  obtain ⟨j, hj, hdiag⟩ := vague_diagonal_selection
    (fun i j => dimensionalBlowup m μ x (r i j)) ν ξ
    (fun i j => regular_dimensionalBlowup μ inferInstance x (hr i j))
    (fun i => (hν i).1) hξ hrow hlim P hP
  refine ⟨hξ, hξ0, fun i => r i (j i), fun i => hr i (j i), ?_, hdiag⟩
  exact squeeze_zero (fun i => (hr i (j i)).le) (fun i => (hj i).2.le)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem tangent_closed
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (ν : ℕ → Measure (Euclidean n)) (ξ : Measure (Euclidean n))
    (hν : ∀ i, IsTangentMeasure μ (ν i) x)
    (hlim : Measure.WeaklyConverges ν ξ) (hξ : ξ.Regular) (hξ0 : ξ ≠ 0) :
    IsTangentMeasure μ ξ x := by
  classical
  choose r c hr hc hctop hr0 hrow using fun i => (hν i).2.2
  let P (i j : ℕ) := r i j < 1 / ((i : ℝ) + 1)
  have hP (i : ℕ) : ∀ᶠ j in atTop, P i j :=
    (hr0 i).eventually_lt_const (by positivity)
  obtain ⟨j, hj, hdiag⟩ := vague_diagonal_selection
    (fun i j => c i j • μ.map (blowUpMap x (r i j))) ν ξ
    (fun i j => regular_smul_map_blowUp inferInstance x (hr i j).ne' (hctop i j))
    (fun i => (hν i).1) hξ hrow hlim P hP
  refine ⟨hξ, hξ0, fun i => r i (j i), fun i => c i (j i),
    fun i => hr i (j i), fun i => hc i (j i), fun i => hctop i (j i), ?_, hdiag⟩
  exact squeeze_zero (fun i => (hr i (j i)).le) (fun i => (hj i).2.le)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem dimensionalTangent_dilate (μ ν : Measure (Euclidean n))
    [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hν : IsDimensionalTangent m μ ν x) (r : ℝ) (hr : 0 < r) :
    IsDimensionalTangent m μ (dimensionalBlowup m ν 0 r) x := by
  exact hν.dilate hr

theorem dimensionalTangent_nonempty_compact_of_ball_bounds
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    {p q R : ℝ} (hp : 0 < p) (hq : 0 < q) (hR : 0 < R)
    (hup : ∀ t, 0 < t → t < R → μ (closedBall x t) ≤ ENNReal.ofReal (q * t ^ m))
    (hlo : ∀ t, 0 < t → t < R → ENNReal.ofReal (p * t ^ m) ≤ μ (closedBall x t)) :
    (∃ ν, IsDimensionalTangent m μ ν x) ∧
    ∀ ν : ℕ → Measure (Euclidean n),
      (∀ i, IsDimensionalTangent m μ (ν i) x) →
      ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧
        IsDimensionalTangent m μ ξ x ∧ Measure.WeaklyConverges (ν ∘ φ) ξ := by
  classical
  constructor
  · obtain ⟨φ, ν, hφ, hν, hν0, hlim, _⟩ :=
      exists_dimensional_tangent_subseq_of_ball_bounds μ x hp hq hR hup hlo
        (fun i => 1 / ((i : ℝ) + 1)) (fun i => by positivity)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact ⟨ν, hν, hν0, (fun i => 1 / ((φ i : ℝ) + 1)),
      fun i => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop, hlim⟩
  · intro ν hν
    obtain ⟨M⟩ := exists_vagueMetrization n
    letI := M.metric
    choose r hr hr0 hrow using fun i => (hν i).2.2
    let τ (i j : ℕ) : RegularEuclideanMeasure n :=
      ⟨dimensionalBlowup m μ x (r i j), regular_dimensionalBlowup μ inferInstance x (hr i j)⟩
    let ν' (i : ℕ) : RegularEuclideanMeasure n := ⟨ν i, (hν i).1⟩
    have hrow' (i : ℕ) : Tendsto (τ i) atTop (𝓝 (ν' i)) :=
      (M.tendsto_iff (τ i) (ν' i)).mpr (hrow i)
    have hchoose (i : ℕ) : ∃ j, r i j < 1 / ((i : ℝ) + 1) ∧
        dist (τ i j) (ν' i) < 1 / ((i : ℝ) + 1) := by
      have hrad := (hr0 i).eventually_lt_const (show 0 < 1 / ((i : ℝ) + 1) by positivity)
      have hdist := Metric.tendsto_nhds.mp (hrow' i) (1 / ((i : ℝ) + 1)) (by positivity)
      exact (hrad.and hdist).exists
    choose j hjrad hjdist using hchoose
    have hrad : Tendsto (fun i => r i (j i)) atTop (𝓝 0) :=
      squeeze_zero (fun i => (hr i (j i)).le) (fun i => (hjrad i).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hdist : Tendsto (fun i => dist (τ i (j i)) (ν' i)) atTop (𝓝 0) :=
      squeeze_zero (fun i => dist_nonneg) (fun i => (hjdist i).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨φ, ξ, hφ, hξ, hξ0, hlim, _⟩ :=
      exists_dimensional_tangent_subseq_of_ball_bounds μ x hp hq hR hup hlo
        (fun i => r i (j i)) (fun i => hr i (j i)) hrad
    let ξ' : RegularEuclideanMeasure n := ⟨ξ, hξ⟩
    have hlim' : Tendsto (fun i => τ (φ i) (j (φ i))) atTop (𝓝 ξ') :=
      (M.tendsto_iff _ ξ').mpr hlim
    have hνlim := hlim'.congr_dist (hdist.comp hφ.tendsto_atTop)
    exact ⟨φ, ξ, hφ, ⟨hξ, hξ0, fun i => r (φ i) (j (φ i)),
      fun i => hr (φ i) (j (φ i)), hrad.comp hφ.tendsto_atTop, hlim⟩,
      (M.tendsto_iff (ν' ∘ φ) ξ').mp hνlim⟩

theorem dimensionalTangent_nonempty_compact
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ] (x : Euclidean n)
    (hd : HasPositiveFiniteDensityAt m μ x) :
    (∃ ν, IsDimensionalTangent m μ ν x) ∧
    ∀ ν : ℕ → Measure (Euclidean n),
      (∀ i, IsDimensionalTangent m μ (ν i) x) →
      ∃ (φ : ℕ → ℕ) (ξ : Measure (Euclidean n)), StrictMono φ ∧
        IsDimensionalTangent m μ ξ x ∧ Measure.WeaklyConverges (ν ∘ φ) ξ := by
  obtain ⟨p, q, R, hp, hq, hR, hup, hlo⟩ := SUniformAux.ball_bounds_of_mem
    (show x ∈ positiveFiniteDensitySet (m : ℝ) μ from
      ⟨hd.1, lower_le_upper_density (m : ℝ) x, hd.2.2⟩)
  exact dimensionalTangent_nonempty_compact_of_ball_bounds μ x hp hq hR
    (by simpa only [Real.rpow_natCast] using hup)
    (by simpa only [Real.rpow_natCast] using hlo)

end Preiss
