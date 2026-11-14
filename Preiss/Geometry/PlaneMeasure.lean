module

public import Preiss.Geometry.Planes
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

def flatOn (V : Plane m n) (c : ℝ≥0∞) : Measure (Euclidean n) :=
  c • ((Measure.hausdorffMeasure (m : ℝ))).restrict (V.1 : Set (Euclidean n))

def unitFlat (V : Plane m n) : Measure (Euclidean n) :=
  (flatOn V 1 (closedBall 0 1))⁻¹ • flatOn V 1

theorem unitFlat_closedBall (V : Plane m n) (x : Euclidean n) (hx : x ∈ V.1)
    {r : ℝ} (hr : 0 < r) : unitFlat V (closedBall x r) = ENNReal.ofReal (r ^ m) := by
  sorry

theorem map_hausdorffMeasure_subtype_eq_restrict (V : Plane m n) :
    (Measure.hausdorffMeasure (m : ℝ) : Measure V.1).map
      (fun v : V.1 ↦ (v : Euclidean n)) = ((Measure.hausdorffMeasure (m : ℝ))).restrict (V.1 : Set (Euclidean n)) := by
  sorry

theorem planeMeasure_ball_and_sphere (V : Plane m n) (hm : 0 < m) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : Euclidean n, x ∈ V.1 → ∀ r : ℝ, 0 < r →
      ((Measure.hausdorffMeasure (m : ℝ))).restrict (V.1 : Set (Euclidean n)) (ball x r) =
        ENNReal.ofReal (b * r ^ m) ∧
      ((Measure.hausdorffMeasure (m : ℝ))).restrict (V.1 : Set (Euclidean n)) (sphere x r) = 0 := by sorry

end Preiss
