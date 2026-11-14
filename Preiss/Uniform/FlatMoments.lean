module
public import Preiss.Uniform.FlatMomentGeometry
public import Preiss.Uniform.ConicalCoefficients
public import Preiss.Uniform.MomentForms
public import Preiss.Geometry.Projections
public import Preiss.Geometry.PlaneSymmetry
public import Preiss.Uniform.MomentCovariance

@[expose] public section
namespace Preiss
variable {n m : ℕ}

theorem flat_gaussianMoment_diagonal (V : Plane m n) (j : ℕ) (s : ℝ) (hs : 0 < s)
    (x : Euclidean n) :
    gaussianMomentForm (unitFlat V) (2 * j) s (fun _ => x) =
      s ^ j * ‖proj V x‖ ^ (2 * j) / (j.factorial : ℝ) := by
  by_cases hm : m = 0
  · subst m
    exact flat_gaussianMoment_diagonal_dim_zero V j s x
  by_cases hj : j = 0
  · subst j
    simpa using gaussianMomentForm_unitFlat_zero_diagonal V s hs x
  have hform := conical_even_moment_on_support (unitFlat V) (Nat.pos_of_ne_zero hm)
    (isUnitUniform_unitFlat V) (isConical_unitFlat V) j (Nat.pos_of_ne_zero hj)
    (proj V x) (by rw [unitFlat_support]; exact (V.1.orthogonalProjectionOnto x).property)
  rw [gaussianMomentForm_unitFlat_diagonal_project V (2*j) s hs x,
    gaussianMomentForm_homogeneous_of_isConical (unitFlat V) (isConical_unitFlat V) (2*j) s hs,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, hform]
  have hexp : ((2*j : ℕ) : ℝ)/2 = (j : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_natCast]
  ring

theorem flat_gaussianMoment_odd (V : Plane m n) (k : ℕ) (hk : Odd k)
    (s : ℝ) (hs : 0 < s) : gaussianMomentForm (unitFlat V) k s = 0 := by
  exact gaussianMomentForm_eq_zero_of_odd_of_map_neg (unitFlat V) (unitFlat_map_neg V) k hk s

end Preiss
