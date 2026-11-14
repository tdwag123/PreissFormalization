module
public import Preiss.Uniform.MomentForms
public import Preiss.Geometry.Projections
public import Preiss.Geometry.PlaneMeasure

@[expose] public section
namespace Preiss
variable {n m : ℕ}

theorem flat_gaussianMoment_diagonal (V : Plane m n) (j : ℕ) (s : ℝ) (hs : 0 < s)
    (x : Euclidean n) :
    gaussianMomentForm (unitFlat V) (2 * j) s (fun _ => x) =
      s ^ j * ‖proj V x‖ ^ (2 * j) / (j.factorial : ℝ) := by
  sorry

theorem flat_gaussianMoment_odd (V : Plane m n) (k : ℕ) (hk : Odd k)
    (s : ℝ) (hs : 0 < s) : gaussianMomentForm (unitFlat V) k s = 0 := by
  sorry

end Preiss
