module

public import Preiss.Geometry.Cylinders
public import Preiss.Geometry.PlaneMeasure
public import Preiss.Rectifiability.WeakApproximation.Uniformization
public import Preiss.Rectifiability.WeakApproximation.TwoSided
public import Preiss.Rectifiability.WeakApproximation.Restriction
public import Preiss.Density.PowerComparison
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Covering.Vitali

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

structure HoleFamily (V : Plane m n) (K : Set (Euclidean n))
    (a : Euclidean n) (σ η : ℝ) where
  active : Set ℕ
  center : ℕ → Euclidean n
  radius : ℕ → ℝ
  center_mem : ∀ i ∈ active, center i ∈ V.1
  center_near : ∀ i ∈ active, center i ∈ ball (proj V a) (σ / 4)
  center_out : ∀ i ∈ active, center i ∉ K
  radius_eq : ∀ i ∈ active, radius i = infDist (center i) K
  radius_pos : ∀ i ∈ active, 0 < radius i
  radius_le : ∀ i ∈ active, radius i ≤ η * σ
  disjoint : active.Pairwise (fun i j ↦ Disjoint
    (ball (center i) (4 * radius i) ∩ (V.1 : Set (Euclidean n)))
    (ball (center j) (4 * radius j) ∩ (V.1 : Set (Euclidean n))))
  cover : (ball (proj V a) (σ / 4) ∩ (V.1 : Set (Euclidean n))) \ K ⊆
    ⋃ i ∈ active, ball (center i) (20 * radius i)

set_option maxHeartbeats 800000 in
theorem exists_holeFamily_of_compact (V : Plane m n) (K : Set (Euclidean n))
    (a : Euclidean n) {σ η : ℝ} (hK : IsCompact K) (hKn : K.Nonempty)
    (hσ : 0 < σ) (hη : 0 < η)
    (hclose : ∀ p : Euclidean n, p ∈ V.1 → p ∈ ball (proj V a) σ →
      infDist p K ≤ η * σ) : Nonempty (HoleFamily V K a σ η) := by
  classical
  let S : Set V.1 := {p | (p : Euclidean n) ∈ ball (proj V a) (σ / 4) ∧
    (p : Euclidean n) ∉ K}
  let r : V.1 → ℝ := fun p ↦ 4 * infDist (p : Euclidean n) K
  have hrpos (p : V.1) (hp : p ∈ S) : 0 < r p := by
    dsimp [r]
    exact mul_pos (by norm_num) ((hK.isClosed.notMem_iff_infDist_pos hKn).mp hp.2)
  have hrbound (p : V.1) (hp : p ∈ S) : r p ≤ 4 * (η * σ) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact hclose p p.property (ball_subset_ball (by linarith) hp.1)
  obtain ⟨U, hUS, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id r (4 * (η * σ))
      hrbound 5 (by norm_num)
  have hcount : U.Countable := hdisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun p hp ↦ ⟨p, mem_ball_self (hrpos p (hUS hp))⟩)
  letI : Countable U := hcount.to_subtype
  letI : Encodable U := Encodable.ofCountable U
  let f : ℕ → V.1 := fun i ↦ ((Encodable.decode (α := U) i).map Subtype.val).getD 0
  have hfe (u : U) : f (Encodable.encode u) = (u : V.1) := by simp [f]
  let A : Set ℕ := range (Encodable.encode : U → ℕ)
  let c : ℕ → Euclidean n := fun i ↦ f i
  let ρ : ℕ → ℝ := fun i ↦ infDist (c i) K
  have hce (u : U) : c (Encodable.encode u) = ((u : V.1) : Euclidean n) := by
    dsimp [c]; rw [hfe]
  refine ⟨{
    active := A
    center := c
    radius := ρ
    center_mem := fun i _ ↦ (f i).property
    center_near := ?_
    center_out := ?_
    radius_eq := fun _ _ ↦ rfl
    radius_pos := ?_
    radius_le := ?_
    disjoint := ?_
    cover := ?_
  }⟩
  · rintro i ⟨u, rfl⟩
    rw [hce]
    exact (hUS u.property).1
  · rintro i ⟨u, rfl⟩
    rw [hce]
    exact (hUS u.property).2
  · rintro i ⟨u, rfl⟩
    dsimp [ρ]
    rw [hce]
    exact (hK.isClosed.notMem_iff_infDist_pos hKn).mp (hUS u.property).2
  · rintro i ⟨u, rfl⟩
    dsimp [ρ]
    rw [hce]
    exact hclose u u.val.property (ball_subset_ball (by linarith) (hUS u.property).1)
  · rintro i ⟨u, rfl⟩ j ⟨v, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro x hxu hxv
    have huv : (u : V.1) ≠ (v : V.1) := by
      intro heq
      exact hne (congrArg Encodable.encode (Subtype.ext heq))
    have hh := hdisj u.property v.property huv
    have hx1 : (⟨x, hxu.2⟩ : V.1) ∈ ball (u : V.1) (r u) := by
      change dist x (u : Euclidean n) < r u
      simpa only [ρ, hce, r, mem_ball] using hxu.1
    have hx2 : (⟨x, hxu.2⟩ : V.1) ∈ ball (v : V.1) (r v) := by
      change dist x (v : Euclidean n) < r v
      simpa only [ρ, hce, r, mem_ball] using hxv.1
    exact Set.disjoint_left.mp hh hx1 hx2
  · intro x hx
    let p : V.1 := ⟨x, hx.1.2⟩
    have hp : p ∈ S := ⟨hx.1.1, hx.2⟩
    obtain ⟨v, hvU, hv⟩ := hcover p hp
    have hmem := hv (mem_ball_self (hrpos p hp))
    refine mem_iUnion.mpr ⟨Encodable.encode (⟨v, hvU⟩ : U), mem_iUnion.mpr ⟨⟨⟨v, hvU⟩, rfl⟩, ?_⟩⟩
    change dist x (c (Encodable.encode (⟨v, hvU⟩ : U))) <
      20 * infDist (c (Encodable.encode (⟨v, hvU⟩ : U))) K
    rw [hce (⟨v, hvU⟩ : U)]
    change dist x (v : Euclidean n) < 5 * (4 * infDist (v : Euclidean n) K) at hmem
    linarith

set_option maxHeartbeats 800000 in
theorem holeFamily_mass_lower_bound (V : Plane m n) (K : Set (Euclidean n))
    (a : Euclidean n) {σ η b : ℝ} (hσ : 0 < σ) (hb : 0 < b)
    (hKnull : (Measure.hausdorffMeasure (m : ℝ)) K = 0)
    (hball : ∀ x : Euclidean n, x ∈ V.1 → ∀ r : ℝ, 0 < r →
      (Measure.hausdorffMeasure (m : ℝ)).restrict (V.1 : Set (Euclidean n)) (ball x r) =
        ENNReal.ofReal (b * r ^ m)) (d : HoleFamily V K a σ η) :
    ENNReal.ofReal ((1 / 80 ^ m) * σ ^ m) ≤
      ∑' i : d.active, ENNReal.ofReal (d.radius i ^ m) := by
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (m : ℝ)
  let μ := H.restrict (V.1 : Set (Euclidean n))
  have hμK : μ K = 0 := le_antisymm ((Measure.restrict_le_self K).trans hKnull.le) bot_le
  have hVa : proj V a ∈ V.1 := (V.1.orthogonalProjectionOnto a).property
  have hmass : ENNReal.ofReal (b * (σ / 4) ^ m) =
      μ ((ball (proj V a) (σ / 4) ∩ (V.1 : Set (Euclidean n))) \ K) := by
    rw [measure_sdiff_null hμK]
    have hV : MeasurableSet (V.1 : Set (Euclidean n)) := V.1.closed_of_finiteDimensional.measurableSet
    have heq : μ (ball (proj V a) (σ / 4) ∩ (V.1 : Set (Euclidean n))) =
        μ (ball (proj V a) (σ / 4)) := by
      dsimp [μ]
      rw [Measure.restrict_apply (isOpen_ball.measurableSet.inter hV),
        Measure.restrict_apply isOpen_ball.measurableSet]
      simp only [inter_assoc, inter_self]
    rw [heq]
    exact (hball _ hVa _ (by positivity)).symm
  have hsum : ENNReal.ofReal (b * (σ / 4) ^ m) ≤
      ∑' i : d.active, ENNReal.ofReal (b * (20 * d.radius i) ^ m) := by
    rw [hmass]
    calc
      μ ((ball (proj V a) (σ / 4) ∩ (V.1 : Set (Euclidean n))) \ K) ≤
          μ (⋃ i : d.active, ball (d.center i) (20 * d.radius i)) := by
        apply measure_mono
        simpa only [iUnion_subtype] using d.cover
      _ ≤ ∑' i : d.active, μ (ball (d.center i) (20 * d.radius i)) := measure_iUnion_le _
      _ = _ := tsum_congr fun i ↦ hball _ (d.center_mem i i.property) _
        (mul_pos (by norm_num) (d.radius_pos i i.property))
  let A : ℝ≥0∞ := ENNReal.ofReal (b * 20 ^ m)
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hleft : ENNReal.ofReal (b * (σ / 4) ^ m) =
      A * ENNReal.ofReal ((1 / 80 ^ m) * σ ^ m) := by
    dsimp [A]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have heq : (80 : ℝ) ^ m = 20 ^ m * 4 ^ m := by rw [← mul_pow]; norm_num
    rw [div_pow, heq]
    field_simp
  have hright : (∑' i : d.active, ENNReal.ofReal (b * (20 * d.radius i) ^ m)) =
      A * (∑' i : d.active, ENNReal.ofReal (d.radius i ^ m)) := by
    simp only [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (show 0 ≤ b * 20 ^ m by positivity),
      ENNReal.tsum_mul_left, A]
  rw [hleft, hright] at hsum
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ A⁻¹ from bot_le)
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hA0 hAtop, one_mul] using hh

theorem HoleFamily.disjoint_cylinders {V : Plane m n} {K : Set (Euclidean n)}
    {a : Euclidean n} {σ η : ℝ} (d : HoleFamily V K a σ η)
    {i j : ℕ} (hi : i ∈ d.active) (hj : j ∈ d.active) (hij : i ≠ j) :
    Disjoint {x | dist (proj V x) (d.center i) < 4 * d.radius i}
      {x | dist (proj V x) (d.center j) < 4 * d.radius j} := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hp : proj V x ∈ V.1 := (V.1.orthogonalProjectionOnto x).property
  exact Set.disjoint_left.mp (d.disjoint hi hj hij) ⟨hxi, hp⟩ ⟨hxj, hp⟩

theorem exists_projection_hole_disk_family (m n : ℕ) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V : Plane m n) (K : Set (Euclidean n))
      (a : Euclidean n) (σ η : ℝ), IsCompact K → K.Nonempty →
      K ⊆ (V.1 : Set (Euclidean n)) → (Measure.hausdorffMeasure (m : ℝ)) K = 0 → 0 < σ → 0 < η → η < 1 →
      (∀ p : Euclidean n, p ∈ V.1 → p ∈ ball (proj V a) σ → infDist p K ≤ η * σ) →
      ∃ d : HoleFamily V K a σ η,
        ENNReal.ofReal (c * σ ^ m) ≤ ∑' i : d.active, ENNReal.ofReal (d.radius i ^ m) := by
  refine ⟨1 / 80 ^ m, by positivity, ?_⟩
  intro V K a σ η hK hKn hKV hKnull hσ hη hη1 hclose
  obtain ⟨d⟩ := exists_holeFamily_of_compact V K a hK hKn hσ hη hclose
  obtain ⟨b, hb, hball⟩ := planeMeasure_ball_and_sphere V hm
  refine ⟨d, holeFamily_mass_lower_bound V K a hσ hb hKnull ?_ d⟩
  intro x hx r hr
  exact (hball x hx r hr).1

theorem mem_half_ball_of_tube_and_projected_distance
    (V : Plane m n) (a z p : Euclidean n) {σ β : ℝ}
    (hσ : 0 < σ) (hβ : β < 1 / 8)
    (htube : infDist (z - a) (V.1 : Set (Euclidean n)) ≤ β * σ)
    (hp : p ∈ ball (proj V a) (σ / 4))
    (hd : dist (proj V z) p ≤ β * σ) : z ∈ ball a (σ / 2) := by
  have hres : ‖(z - a) - proj V (z - a)‖ =
      infDist (z - a) (V.1 : Set (Euclidean n)) := by
    change ‖(z - a) - V.1.starProjection (z - a)‖ = _
    rw [Submodule.starProjection_minimal, infDist_eq_iInf]
    rfl
  have hpnorm : ‖proj V (z - a)‖ = dist (proj V z) (proj V a) := by
    change ‖V.1.starProjection (z - a)‖ =
      dist (V.1.starProjection z) (V.1.starProjection a)
    rw [map_sub, dist_eq_norm]
  have hnorm : ‖z - a‖ ≤ ‖(z - a) - proj V (z - a)‖ + ‖proj V (z - a)‖ := by
    simpa only [sub_add_cancel] using norm_add_le ((z - a) - proj V (z - a)) (proj V (z - a))
  rw [hres, hpnorm] at hnorm
  have htri := dist_triangle (proj V z) p (proj V a)
  have hp' : dist p (proj V a) < σ / 4 := hp
  have hsmall : β * σ < σ / 8 := by nlinarith
  show dist z a < σ / 2
  rw [dist_eq_norm]
  linarith

theorem projected_distance_le_of_lower_mass (μ : Measure (Euclidean n))
    (V : Plane m n) (G : Set (Euclidean n)) (a p : Euclidean n) {σ η b : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hη1 : η < 1) (hp : p - a ∈ V.1)
    (hnear : p ∈ ball a σ)
    (hlower : ENNReal.ofReal b ≤ μ (ball p (η * σ)))
    (herror : μ (ball a (2 * σ) \ G) < ENNReal.ofReal b) :
    infDist (proj V p) (proj V '' (G ∩ closedBall a (2 * σ))) ≤ η * σ := by
  have hησ : η * σ < σ := mul_lt_of_lt_one_left hσ hη1
  have hball : ball p (η * σ) ⊆ ball a (2 * σ) := by
    intro q hq
    have hqp : dist q p < η * σ := hq
    have hpa : dist p a < σ := hnear
    have hh := dist_triangle q p a
    change dist q a < 2 * σ
    linarith
  have hnonempty : (ball p (η * σ) ∩ G).Nonempty := by
    by_contra hnone
    have hsub : ball p (η * σ) ⊆ ball a (2 * σ) \ G := by
      intro q hq
      exact ⟨hball hq, fun hqG ↦ hnone ⟨q, hq, hqG⟩⟩
    exact (not_lt_of_ge hlower) ((measure_mono hsub).trans_lt herror)
  obtain ⟨q, hqp, hqG⟩ := hnonempty
  have hqimage : proj V q ∈ proj V '' (G ∩ closedBall a (2 * σ)) :=
    ⟨q, ⟨hqG, ball_subset_closedBall (hball hqp)⟩, rfl⟩
  have hdist : dist (proj V p) (proj V q) ≤ dist p q := by
    change dist (V.1.starProjection p) (V.1.starProjection q) ≤ dist p q
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact V.1.norm_starProjection_apply_le (p - q)
  have hdistpq : dist p q < η * σ := by simpa only [mem_ball, dist_comm] using hqp
  exact ((infDist_le_dist_of_mem hqimage).trans hdist).trans hdistpq.le

theorem tsum_hole_radii_bad_indices_le (μ : Measure (Euclidean n))
    (J : Set ℕ) (ρ : ℕ → ℝ) (A : ℕ → Set (Euclidean n))
    (D : Set (Euclidean n)) {δ t σ : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hσ : 0 < σ)
    (hA : ∀ i ∈ J, MeasurableSet (A i))
    (hdisj : J.Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hsub : ∀ i ∈ J, A i ⊆ D)
    (hlower : ∀ i ∈ J, ENNReal.ofReal (δ * ρ i ^ m / 2 ^ m) ≤ μ (A i))
    (hρ : ∀ i ∈ J, 0 ≤ ρ i) (hD : μ D ≤ ENNReal.ofReal (t * σ ^ m)) :
    (∑' i : J, ENNReal.ofReal (ρ i ^ m)) ≤
      ENNReal.ofReal ((2 ^ m / δ) * t * σ ^ m) := by
  have hpair : Pairwise (fun i j : J ↦ Disjoint (A i) (A j)) := by
    intro i j hij
    exact hdisj i.property j.property (fun hh ↦ hij (Subtype.ext hh))
  have hmeasure : (∑' i : J, μ (A i)) ≤ μ D := by
    rw [← measure_iUnion hpair (fun i : J ↦ hA i i.property)]
    exact measure_mono (iUnion_subset fun i : J ↦ hsub i i.property)
  have hcoeff (i : J) : ENNReal.ofReal (ρ i ^ m) ≤
      ENNReal.ofReal (2 ^ m / δ) * μ (A i) := by
    calc
      ENNReal.ofReal (ρ i ^ m) =
          ENNReal.ofReal ((2 ^ m / δ) * (δ * ρ i ^ m / 2 ^ m)) := by
        congr 1
        field_simp [hδ.ne']
      _ = ENNReal.ofReal (2 ^ m / δ) * ENNReal.ofReal (δ * ρ i ^ m / 2 ^ m) :=
        ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (2 ^ m / δ) * μ (A i) :=
        mul_le_mul_of_nonneg_left (hlower i i.property) bot_le
  calc
    (∑' i : J, ENNReal.ofReal (ρ i ^ m)) ≤
        ∑' i : J, ENNReal.ofReal (2 ^ m / δ) * μ (A i) := ENNReal.tsum_le_tsum hcoeff
    _ = ENNReal.ofReal (2 ^ m / δ) * ∑' i : J, μ (A i) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (2 ^ m / δ) * μ D := mul_le_mul_of_nonneg_left hmeasure bot_le
    _ ≤ ENNReal.ofReal (2 ^ m / δ) * ENNReal.ofReal (t * σ ^ m) :=
      mul_le_mul_of_nonneg_left hD bot_le
    _ = ENNReal.ofReal ((2 ^ m / δ) * t * σ ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

set_option maxHeartbeats 800000 in
theorem exists_column_disjoint_balls :
    ∃ c η₀ : ℝ, 0 < c ∧ 0 < η₀ ∧ ∀ (m n : ℕ) (V W : Plane m n)
      (F : Set (Euclidean n)) (a z p w : Euclidean n) (ρ σ η : ℝ),
      F.Nonempty → 0 < ρ → 0 < σ → 0 < η → η < η₀ → ρ ≤ η * σ →
      z ∈ ball a (σ / 2) → dist (proj V z) p = ρ →
      w ∈ W.1 → ‖w‖ = 1 → ‖proj V w‖ ≤ 32 * η →
      (∀ y : Euclidean n, y - z ∈ W.1 → y ∈ ball z (ρ / (8 * η)) →
        infDist y F < ρ / 8) →
      ∃ Q : Finset (Euclidean n),
        c / η ≤ (Q.card : ℝ) ∧ (↑Q : Set (Euclidean n)) ⊆ F ∧
        (↑Q : Set (Euclidean n)).Pairwise (fun u v ↦ Disjoint
          (ball u (ρ / 8)) (ball v (ρ / 8))) ∧
        ∀ q ∈ Q, ball q (ρ / 8) ⊆ cylinder V p (4 * ρ) ∩ ball a σ := by
  classical
  refine ⟨1 / 32, 1 / 32, by norm_num, by norm_num, ?_⟩
  intro m n V W F a z p w ρ σ η hF hρ hσ hη hηsmall hρσ hz hd hw hnorm hproj happ
  let N : ℕ := ⌈1 / (32 * η)⌉₊
  have hx : 1 < 1 / (32 * η) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
  have hNlow : 1 / (32 * η) ≤ (N : ℝ) := Nat.le_ceil _
  have hNhigh : (N : ℝ) < 1 / (16 * η) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 1 / (32 * η) by positivity)
    dsimp [N]
    have heq : 1 / (16 * η) = 2 * (1 / (32 * η)) := by field_simp; ring
    rw [heq]
    linarith
  let t : Fin N → ℝ := fun i ↦ ((i.val : ℝ) + 1) * ρ
  let y : Fin N → Euclidean n := fun i ↦ z + t i • w
  have htpos (i : Fin N) : 0 < t i := by dsimp [t]; positivity
  have htbound (i : Fin N) : t i < ρ / (16 * η) := by
    have hi : (i.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast i.isLt
    have hmul := mul_le_mul_of_nonneg_right hi hρ.le
    have hstrict := mul_lt_mul_of_pos_right hNhigh hρ
    dsimp [t]
    calc
      ((i.val : ℝ) + 1) * ρ ≤ (N : ℝ) * ρ := hmul
      _ < (1 / (16 * η)) * ρ := hstrict
      _ = ρ / (16 * η) := by ring
  have hydist (i : Fin N) : dist (y i) z = t i := by
    simp [y, dist_eq_norm, norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos (htpos i)]
  have hy (i : Fin N) : ∃ q ∈ F, dist (y i) q < ρ / 8 := by
    apply (infDist_lt_iff hF).mp
    apply happ
    · simpa [y] using W.1.smul_mem (t i) hw
    · show dist (y i) z < ρ / (8 * η)
      rw [hydist]
      have : ρ / (16 * η) < ρ / (8 * η) := by
        apply div_lt_div_of_pos_left hρ <;> nlinarith
      exact (htbound i).trans this
  choose q hqF hqclose using hy
  have hsep (i j : Fin N) (hij : i ≠ j) : ρ * (3 / 4) < dist (q i) (q j) := by
    have hysep : ρ ≤ dist (y i) (y j) := by
      have hdij : dist (y i) (y j) = |t i - t j| := by
        rw [dist_eq_norm]
        have heq : y i - y j = (t i - t j) • w := by dsimp [y]; rw [sub_smul]; abel
        rw [heq, norm_smul, hnorm, mul_one, Real.norm_eq_abs]
      rw [hdij]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · have hi : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hlt
        have hh := mul_le_mul_of_nonneg_right hi hρ.le
        have hneg : t i - t j ≤ 0 := by dsimp [t]; nlinarith
        rw [abs_of_nonpos hneg]
        dsimp [t]
        nlinarith
      · have hi : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hlt
        have hh := mul_le_mul_of_nonneg_right hi hρ.le
        have hpos : 0 ≤ t i - t j := by dsimp [t]; nlinarith
        rw [abs_of_nonneg hpos]
        dsimp [t]
        nlinarith
    have hh := dist_triangle4 (y i) (q i) (q j) (y j)
    rw [dist_comm (q j) (y j)] at hh
    linarith [hqclose i, hqclose j]
  have hinj : Function.Injective q := by
    intro i j heq
    by_contra hne
    have hh := hsep i j hne
    rw [heq, dist_self] at hh
    nlinarith
  let Q : Finset (Euclidean n) := Finset.univ.image q
  have hcard : Q.card = N := by simp [Q, Finset.card_image_of_injective _ hinj]
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · rw [hcard]
    convert hNlow using 1 <;> ring
  · intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact hqF i
  · intro u hu v hv huv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    apply ball_disjoint_ball
    have hh := hsep i j (fun heq ↦ huv (congrArg q heq))
    linarith
  · intro u hu x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    have hxy : dist x (y i) < ρ / 4 := by
      have hh := dist_triangle x (q i) (y i)
      rw [dist_comm (q i) (y i)] at hh
      have hx' : dist x (q i) < ρ / 8 := hx
      linarith [hqclose i]
    have hprojLip : dist (proj V x) (proj V (y i)) ≤ dist x (y i) := by
      change dist (V.1.starProjection x) (V.1.starProjection (y i)) ≤ dist x (y i)
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact V.1.norm_starProjection_apply_le _
    have hprojray : dist (proj V (y i)) (proj V z) = t i * ‖proj V w‖ := by
      change dist (V.1.starProjection (z + t i • w)) (V.1.starProjection z) = _
      rw [map_add, map_smul, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (htpos i)]
      rfl
    have htprod : t i * (32 * η) < 2 * ρ := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 16 * η)).mp (htbound i)
      nlinarith
    constructor
    · change dist (proj V x) p < 4 * ρ
      have hh := dist_triangle4 (proj V x) (proj V (y i)) (proj V z) p
      rw [hd, hprojray] at hh
      have hmul := mul_le_mul_of_nonneg_left hproj (htpos i).le
      linarith
    · show dist x a < σ
      have hh := dist_triangle4 x (y i) z a
      rw [hydist] at hh
      have hz' : dist z a < σ / 2 := hz
      have htσ : t i < σ / 16 := by
        have hh := (lt_div_iff₀ (by positivity : 0 < 16 * η)).mp (htbound i)
        nlinarith
      have hρsmall : ρ < σ / 32 := lt_of_le_of_lt hρσ (by nlinarith)
      linarith

set_option maxHeartbeats 800000 in
theorem false_of_column_mass_exceeds_upper_bound
    (μ : Measure (Euclidean n)) (I : Set ℕ) (ρ : ℕ → ℝ)
    (Q : ℕ → Finset (Euclidean n)) (a : Euclidean n) {δ c₁ c₂ η C σ : ℝ}
    (hδ : 0 < δ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hη : 0 < η)
    (hC : 0 < C) (hσ : 0 < σ)
    (hsmall : C < c₁ * c₂ * δ / (8 ^ m * η))
    (hr : ∀ i ∈ I, 0 < ρ i)
    (hrsum : ENNReal.ofReal (c₂ * σ ^ m) ≤ ∑' i : I, ENNReal.ofReal (ρ i ^ m))
    (hcard : ∀ i ∈ I, c₁ / η ≤ ((Q i).card : ℝ))
    (hdisj : Pairwise (fun u v : {i : ℕ // i ∈ I} × Euclidean n ↦
      u.2 ∈ Q u.1 → v.2 ∈ Q v.1 → Disjoint
        (ball u.2 (ρ u.1 / 8)) (ball v.2 (ρ v.1 / 8))))
    (hsub : ∀ i ∈ I, ∀ q ∈ Q i, ball q (ρ i / 8) ⊆ ball a σ)
    (hlower : ∀ i ∈ I, ∀ q ∈ Q i,
      ENNReal.ofReal (δ * (ρ i / 8) ^ m) ≤ μ (ball q (ρ i / 8)))
    (hupper : μ (ball a σ) ≤ ENNReal.ofReal (C * σ ^ m)) : False := by
  classical
  let T := Σ i : I, ↥(Q i)
  let B : T → Set (Euclidean n) := fun u ↦ ball u.2 (ρ u.1 / 8)
  have hinj : Function.Injective (fun u : T ↦ (u.1, (u.2 : Euclidean n))) := by
    intro u v huv
    rcases u with ⟨i, q⟩
    rcases v with ⟨j, s⟩
    have hij : i = j := congrArg Prod.fst huv
    subst j
    have hqs : q = s := Subtype.ext (congrArg Prod.snd huv)
    subst s
    rfl
  have hpair : Pairwise (fun u v : T ↦ Disjoint (B u) (B v)) := by
    intro u v huv
    have hne : (u.1, (u.2 : Euclidean n)) ≠ (v.1, (v.2 : Euclidean n)) := fun hh ↦ huv (hinj hh)
    change Disjoint (ball (u.2 : Euclidean n) (ρ u.1 / 8))
      (ball (v.2 : Euclidean n) (ρ v.1 / 8))
    exact @hdisj (u.1, (u.2 : Euclidean n)) (v.1, (v.2 : Euclidean n)) hne
      u.2.property v.2.property
  have hmeasure : (∑' u : T, μ (B u)) ≤ μ (ball a σ) := by
    rw [← measure_iUnion hpair (fun _ ↦ isOpen_ball.measurableSet)]
    exact measure_mono (iUnion_subset fun u ↦ hsub u.1 u.1.property u.2 u.2.property)
  let κ : ℝ := c₁ * δ / (8 ^ m * η)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcol (i : I) : ENNReal.ofReal (κ * ρ i ^ m) ≤
      ∑' q : Q i, μ (B ⟨i, q⟩) := by
    have hρi : 0 < ρ i := hr i i.property
    have hδr : 0 ≤ δ * (ρ i / 8) ^ m := by positivity
    have halgebra : κ * ρ i ^ m = (c₁ / η) * (δ * (ρ i / 8) ^ m) := by
      dsimp [κ]
      rw [div_pow]
      field_simp [hη.ne'] <;> ring
    calc
      ENNReal.ofReal (κ * ρ i ^ m) ≤
          ENNReal.ofReal ((Q i).card * (δ * (ρ i / 8) ^ m)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [halgebra]
        exact mul_le_mul_of_nonneg_right (hcard i i.property) hδr
      _ = (Q i).card * ENNReal.ofReal (δ * (ρ i / 8) ^ m) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ = ∑' q : Q i, ENNReal.ofReal (δ * (ρ i / 8) ^ m) := by
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ ∑' q : Q i, μ (B ⟨i, q⟩) := ENNReal.tsum_le_tsum fun q ↦
        hlower i i.property q q.property
  have hsum : ENNReal.ofReal κ * (∑' i : I, ENNReal.ofReal (ρ i ^ m)) ≤ μ (ball a σ) := by
    calc
      ENNReal.ofReal κ * (∑' i : I, ENNReal.ofReal (ρ i ^ m)) =
          ∑' i : I, ENNReal.ofReal (κ * ρ i ^ m) := by
        simp only [ENNReal.ofReal_mul hκ.le, ENNReal.tsum_mul_left]
      _ ≤ ∑' i : I, ∑' q : Q i, μ (B ⟨i, q⟩) := ENNReal.tsum_le_tsum hcol
      _ = ∑' u : T, μ (B u) := (ENNReal.tsum_sigma' (fun u : T ↦ μ (B u))).symm
      _ ≤ μ (ball a σ) := hmeasure
  have hmass : ENNReal.ofReal (κ * (c₂ * σ ^ m)) ≤ ENNReal.ofReal (C * σ ^ m) := by
    rw [ENNReal.ofReal_mul hκ.le]
    exact ((mul_le_mul_of_nonneg_left hrsum bot_le).trans hsum).trans hupper
  have hthreshold : C < κ * c₂ := by
    convert hsmall using 1 <;> dsimp [κ] <;> ring
  have hstrict : ENNReal.ofReal (C * σ ^ m) < ENNReal.ofReal (κ * (c₂ * σ ^ m)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have hh := mul_lt_mul_of_pos_right hthreshold (pow_pos hσ m)
    simpa only [mul_assoc] using hh
  exact not_lt_of_ge hmass hstrict

theorem false_of_null_projections_and_uniform_weakApproximation
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hpos : 0 < (Measure.hausdorffMeasure (m : ℝ)) E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞)
    (hu : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), UpperPowerBoundAt m (((Measure.hausdorffMeasure (m : ℝ))).restrict E) x)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x)
    (hproj : ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' E) = 0) : False := by sorry

end Preiss
