module

public import Preiss.Rectifiability.MarstrandMattila.Packing

/-! # The geometric packing contradiction for two-sided approximation -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}


set_option maxHeartbeats 3000000 in
theorem false_of_compact_twoSided_approximation
    (hm : 0 < m) (μ : Measure (Euclidean n)) (F : Set (Euclidean n))
    {δ R₀ C : ℝ} (hδ : 0 < δ) (hR₀ : 0 < R₀) (hC : 0 < C)
    (hlower : ∀ x ∈ F, ∀ r : ℝ, 0 < r → r < R₀ →
      ENNReal.ofReal (δ * r ^ m) ≤ μ (ball x r))
    (hcompact : ∀ η : ℝ, 0 < η → η < 1 →
      ∃ (G : Set (Euclidean n)) (γ R : ℝ), IsCompact G ∧ G ⊆ F ∧
        0 < γ ∧ 0 < R ∧ R < R₀ ∧ TwoSidedApproximation m μ F G η γ R ∧
        ∀ t : ℝ, 0 < t → ∃ (a : Euclidean n) (R' : ℝ), a ∈ G ∧ 0 < R' ∧
          ∀ r : ℝ, 0 < r → r < R' →
            μ (ball a r) ≤ ENNReal.ofReal (C * r ^ m) ∧
            μ (ball a (2 * r) \ G) ≤ ENNReal.ofReal (t * r ^ m))
    (hproj : ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' F) = 0) :
    False := by
  classical
  obtain ⟨c₂, hc₂, hholes⟩ := exists_projection_hole_disk_family m n hm
  obtain ⟨c₁, β₀, hc₁, hβ₀, hcolumns⟩ := exists_column_disjoint_balls
  let β := min (β₀ / 2) (min (1 / 16) (c₁ * c₂ * δ / (4 * 8 ^ m * C)))
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ₀' : β < β₀ := (min_le_left _ _).trans_lt (by linarith)
  have hβsmall : β < 1 / 8 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hβbound : β ≤ c₁ * c₂ * δ / (4 * 8 ^ m * C) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : C < c₁ * (c₂ / 2) * δ / (8 ^ m * β) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * 8 ^ m * C)).mp hβbound
    have hpos : 0 < 8 ^ m * β * C := by positivity
    nlinarith
  let η := β / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 := by dsimp [η]; linarith
  obtain ⟨G, γ, R, hG, hGF, hγ, hR, hRR₀, happ, hpoint⟩ := hcompact η hη hη1
  let t := min (γ * β ^ m / 2) (c₂ * δ / (4 * 2 ^ m))
  have ht : 0 < t := by dsimp [t]; positivity
  have htγ : t < γ * β ^ m := (min_le_left _ _).trans_lt (by
    have hh : 0 < γ * β ^ m := by positivity
    linarith)
  have htδ : (2 ^ m / δ) * t ≤ c₂ / 2 := by
    have hh : t ≤ c₂ * δ / (4 * 2 ^ m) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < (4 : ℝ) * 2 ^ m)).mp hh
    calc
      (2 ^ m / δ) * t = (2 ^ m * t) / δ := by ring
      _ ≤ c₂ / 2 := (div_le_iff₀ hδ).mpr (by nlinarith)
  obtain ⟨a, R', ha, hR', hbase⟩ := hpoint t ht
  let σ := min (R / 4) (R' / 2)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσR : 2 * σ < R := by have := min_le_left (R / 4) (R' / 2); dsimp [σ]; linarith
  have hσR' : σ < R' := (min_le_right _ _).trans_lt (by linarith)
  have hσR₀ : σ < R₀ := (show σ < R by linarith).trans hRR₀
  have hmass := hbase σ hσ hσR'
  obtain ⟨V, htube, _, hplane⟩ := happ.2 a ha (2 * σ) (by positivity) hσR
  have hηeq : η * (2 * σ) = β * σ := by dsimp [η]; ring
  rw [hηeq] at htube hplane
  let K := proj V '' (G ∩ closedBall a (2 * σ))
  have hcont : Continuous (proj V) := V.1.starProjection.continuous
  have hK : IsCompact K := (hG.inter_right isClosed_closedBall).image hcont
  have hKn : K.Nonempty := ⟨proj V a, a, ⟨ha, mem_closedBall_self (by positivity)⟩, rfl⟩
  have hKV : K ⊆ (V.1 : Set (Euclidean n)) := by
    rintro _ ⟨z, _, rfl⟩
    exact (V.1.orthogonalProjectionOnto z).property
  have hKnull : (Measure.hausdorffMeasure (m : ℝ)) K = 0 :=
    measure_mono_null (image_mono (fun z hz ↦ hGF hz.1)) (hproj V)
  have herror : μ (ball a (2 * σ) \ G) < ENNReal.ofReal (γ * (β * σ) ^ m) := by
    apply hmass.2.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    rw [mul_pow]
    have hh := mul_lt_mul_of_pos_right htγ (pow_pos hσ m)
    simpa only [mul_assoc] using hh
  have hclose : ∀ p : Euclidean n, p ∈ V.1 → p ∈ ball (proj V a) σ → infDist p K ≤ β * σ := by
    intro p hpV hp
    apply projected_distance_le_of_affine_plane_lower_mass μ V G a p hσ hβ
      (by linarith) hpV hp ?_ herror
    intro z hzV hz
    exact hplane z hzV (ball_subset_ball (by linarith) hz)
  obtain ⟨d, hdrsum⟩ := hholes V K a σ β hK hKn hKV hKnull hσ hβ (by linarith) hclose
  have hGKtube : ∀ z ∈ G ∩ closedBall a (2 * σ),
      infDist (z - a) (V.1 : Set (Euclidean n)) ≤ β * σ := by
    intro z hz
    apply htube
    refine ⟨hGF hz.1, ?_⟩
    apply closedBall_subset_ball (show 2 * σ < 2 * (2 * σ) by linarith)
    exact hz.2
  have hwitness : ∀ i ∈ d.active, ∃ z ∈ G ∩ ball a (σ / 2),
      dist (proj V z) (d.center i) = d.radius i := by
    intro i hi
    obtain ⟨z, hz, heq⟩ := exists_nearest_projected_witness_in_half_ball V G a (d.center i)
      hG ha hσ hβsmall hGKtube (d.center_near i hi)
      (by rw [← d.radius_eq i hi]; exact d.radius_le i hi)
    refine ⟨z, hz, ?_⟩
    rw [heq, d.radius_eq i hi]
  let J : Set ℕ := {i | i ∈ d.active ∧ ∃ q ∈ F ∩ ball a σ,
    dist (proj V q) (d.center i) < d.radius i / 2}
  have hJ : J ⊆ d.active := fun _ hi ↦ hi.1
  have hGK : ∀ x ∈ G ∩ ball a (2 * σ), proj V x ∈ K :=
    fun x hx ↦ ⟨x, ⟨hx.1, ball_subset_closedBall hx.2⟩, rfl⟩
  obtain ⟨q, hq, hqdisj, hqsub⟩ := d.exists_disjoint_charging_balls hσ (by linarith)
    F G J hJ (fun _ hi ↦ hi.2) hGK
  have hrad (i : ℕ) (hi : i ∈ d.active) : d.radius i < σ :=
    (d.radius_le i hi).trans_lt (by nlinarith)
  have hbadmass : (∑' i : J, ENNReal.ofReal (d.radius i ^ m)) ≤
      ENNReal.ofReal ((c₂ / 2) * σ ^ m) := by
    have hh := tsum_hole_radii_bad_indices_le μ J d.radius
      (fun i ↦ ball (q i) (d.radius i / 2)) (ball a (2 * σ) \ G) hδ ht.le hσ
      (fun _ _ ↦ isOpen_ball.measurableSet) hqdisj hqsub
      (fun i hi ↦ by
        have hl := hlower (q i) (hq i hi).1 (d.radius i / 2)
          (by have := d.radius_pos i (hJ hi); positivity)
          (by have := hrad i (hJ hi); linarith)
        simpa only [div_pow, mul_div_assoc] using hl)
      (fun i hi ↦ (d.radius_pos i (hJ hi)).le) hmass.2
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    have hh' := mul_le_mul_of_nonneg_right htδ (pow_nonneg hσ.le m)
    simpa only [mul_assoc] using hh'
  let I := d.active \ J
  have hretained : ENNReal.ofReal ((c₂ / 2) * σ ^ m) ≤
      ∑' i : I, ENNReal.ofReal (d.radius i ^ m) := by
    apply tsum_sdiff_ge_of_small_discarded_sum (fun i ↦ ENNReal.ofReal (d.radius i ^ m))
      d.active J hJ ENNReal.ofReal_ne_top ?_ hbadmass
    have heq : ENNReal.ofReal ((c₂ / 2) * σ ^ m) + ENNReal.ofReal ((c₂ / 2) * σ ^ m) =
        ENNReal.ofReal (c₂ * σ ^ m) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [heq]
    exact hdrsum
  have hcol : ∀ i ∈ I, ∃ Q : Finset (Euclidean n),
      c₁ / β ≤ (Q.card : ℝ) ∧ (↑Q : Set (Euclidean n)) ⊆ F ∧
      (↑Q : Set (Euclidean n)).Pairwise (fun u v ↦ Disjoint
        (ball u (d.radius i / 8)) (ball v (d.radius i / 8))) ∧
      ∀ q ∈ Q, ball q (d.radius i / 8) ⊆ cylinder V (d.center i) (4 * d.radius i) ∩ ball a σ := by
    intro i hi
    have hiA : i ∈ d.active := hi.1
    have hρ := d.radius_pos i hiA
    obtain ⟨z, hz, hdz⟩ := hwitness i hiA
    let r := d.radius i / (8 * β)
    have hr : 0 < r := by dsimp [r]; positivity
    have hrR : r < R := by
      have hh : r ≤ σ / 8 := by
        dsimp [r]
        apply (div_le_iff₀ (by positivity)).mpr
        have hh := d.radius_le i hiA
        nlinarith
      linarith
    obtain ⟨W, _, hnear, _⟩ := happ.2 z hz.1 r hr hrR
    have happ' : ∀ y : Euclidean n, y - z ∈ W.1 →
        y ∈ ball z (d.radius i / (8 * β)) → infDist y F < d.radius i / 8 := by
      intro y hyW hy
      have hh := hnear y hyW hy
      have heq : η * r = d.radius i / 16 := by dsimp [η, r]; field_simp [hβ.ne']; ring
      rw [heq] at hh
      linarith
    have hempty : Disjoint (F ∩ ball a σ) (cylinder V (d.center i) (d.radius i / 2)) := by
      apply Set.disjoint_left.mpr
      intro q hq hcyl
      exact hi.2 ⟨hiA, q, hq, hcyl⟩
    obtain ⟨w, hw, hnorm, hprojw⟩ := exists_unit_small_projection_of_empty_inner_cylinder
      hm V W F a z (d.center i) happ.1 (d.center_mem i hiA) hρ hσ hβ hβsmall
      (d.radius_le i hiA) hz.2 hdz happ' hempty
    exact hcolumns m n V W F a z (d.center i) w (d.radius i) σ β happ.1 hρ hσ hβ
      hβ₀' (d.radius_le i hiA) hz.2 hdz hw hnorm hprojw happ'
  have hchoose : ∀ i : ℕ, ∃ Q : Finset (Euclidean n), i ∈ I →
      c₁ / β ≤ (Q.card : ℝ) ∧ (↑Q : Set (Euclidean n)) ⊆ F ∧
      (↑Q : Set (Euclidean n)).Pairwise (fun u v ↦ Disjoint
        (ball u (d.radius i / 8)) (ball v (d.radius i / 8))) ∧
      ∀ q ∈ Q, ball q (d.radius i / 8) ⊆ cylinder V (d.center i) (4 * d.radius i) ∩ ball a σ := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨Q, hQ⟩ := hcol i hi
      exact ⟨Q, fun _ ↦ hQ⟩
    · exact ⟨∅, fun hh ↦ False.elim (hi hh)⟩
  choose Q hQ using hchoose
  apply false_of_column_mass_exceeds_upper_bound μ I d.radius Q a hδ hc₁
    (show 0 < c₂ / 2 by positivity) hβ hC hσ hsmall
    (fun i hi ↦ d.radius_pos i hi.1) hretained (fun i hi ↦ (hQ i hi).1) ?_
    (fun i hi q hq ↦ fun x hx ↦ ((hQ i hi).2.2.2 q hq hx).2) ?_ hmass.1
  · intro u v huv hu hv
    by_cases hij : u.1 = v.1
    · have hij' : (u.1 : ℕ) = (v.1 : ℕ) := congrArg Subtype.val hij
      have hne : u.2 ≠ v.2 := by
        intro hh
        exact huv (Prod.ext hij hh)
      rw [← hij'] at hv ⊢
      exact (hQ u.1 u.1.property).2.2.1 hu hv hne
    · have hij' : (u.1 : ℕ) ≠ (v.1 : ℕ) := fun hh ↦ hij (Subtype.ext hh)
      apply (d.disjoint_cylinders u.1.property.1 v.1.property.1 hij').mono
      · intro x hx
        exact ((hQ u.1 u.1.property).2.2.2 u.2 hu hx).1
      · intro x hx
        exact ((hQ v.1 v.1.property).2.2.2 v.2 hv hx).1
  · intro i hi q hq
    exact hlower q ((hQ i hi).2.1 hq) (d.radius i / 8)
      (by have := d.radius_pos i hi.1; positivity)
      (by have := hrad i hi.1; linarith)

end Preiss
