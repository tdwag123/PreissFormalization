module

public import Preiss.Geometry.Cylinders
public import Preiss.Geometry.PlaneMeasure
public import Preiss.Rectifiability.WeakApproximation.Uniformization
public import Preiss.Rectifiability.WeakApproximation.TwoSided
public import Preiss.Rectifiability.WeakApproximation.Restriction
public import Preiss.Density.PowerComparison
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

theorem exists_projection_hole_disk_family (m n : ℕ) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V : Plane m n) (K : Set (Euclidean n))
      (a : Euclidean n) (σ η : ℝ), IsCompact K → K.Nonempty →
      K ⊆ (V.1 : Set (Euclidean n)) → (Measure.hausdorffMeasure (m : ℝ)) K = 0 → 0 < σ → 0 < η → η < 1 →
      (∀ p : Euclidean n, p ∈ V.1 → p ∈ ball (proj V a) σ → infDist p K ≤ η * σ) →
      ∃ d : HoleFamily V K a σ η,
        ENNReal.ofReal (c * σ ^ m) ≤ ∑' i : d.active, ENNReal.ofReal (d.radius i ^ m) := by
  sorry

theorem projected_distance_le_of_lower_mass (μ : Measure (Euclidean n))
    (V : Plane m n) (G : Set (Euclidean n)) (a p : Euclidean n) {σ η b : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hη1 : η < 1) (hp : p - a ∈ V.1)
    (hnear : p ∈ ball a σ)
    (hlower : ENNReal.ofReal b ≤ μ (ball p (η * σ)))
    (herror : μ (ball a (2 * σ) \ G) < ENNReal.ofReal b) :
    infDist (proj V p) (proj V '' (G ∩ closedBall a (2 * σ))) ≤ η * σ := by sorry

theorem tsum_hole_radii_bad_indices_le (μ : Measure (Euclidean n))
    (J : Set ℕ) (ρ : ℕ → ℝ) (A : ℕ → Set (Euclidean n))
    (D : Set (Euclidean n)) {δ t σ : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hσ : 0 < σ)
    (hA : ∀ i ∈ J, MeasurableSet (A i))
    (hdisj : J.Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hsub : ∀ i ∈ J, A i ⊆ D)
    (hlower : ∀ i ∈ J, ENNReal.ofReal (δ * ρ i ^ m / 2 ^ m) ≤ μ (A i))
    (hρ : ∀ i ∈ J, 0 ≤ ρ i) (hD : μ D ≤ ENNReal.ofReal (t * σ ^ m)) :
    (∑' i : J, ENNReal.ofReal (ρ i ^ m)) ≤
      ENNReal.ofReal ((2 ^ m / δ) * t * σ ^ m) := by sorry

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
        ∀ q ∈ Q, ball q (ρ / 8) ⊆ cylinder V p (4 * ρ) ∩ ball a σ := by sorry

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
    (hupper : μ (ball a σ) ≤ ENNReal.ofReal (C * σ ^ m)) : False := by sorry

theorem false_of_null_projections_and_uniform_weakApproximation
    (hm : 0 < m) (hmn : m ≤ n) (E : Set (Euclidean n))
    (hE : MeasurableSet E) (hpos : 0 < (Measure.hausdorffMeasure (m : ℝ)) E) (hfin : (Measure.hausdorffMeasure (m : ℝ)) E < ∞)
    (hu : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), UpperPowerBoundAt m (((Measure.hausdorffMeasure (m : ℝ))).restrict E) x)
    (hw : ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict E), WeaklyLinearlyApproximableAt m E x)
    (hproj : ∀ V : Plane m n, (Measure.hausdorffMeasure (m : ℝ)) (proj V '' E) = 0) : False := by sorry

end Preiss
