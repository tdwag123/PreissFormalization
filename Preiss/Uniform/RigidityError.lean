import Preiss.Uniform.FlatAtInfinity.TraceData

/-! # The quadratic error used in flat-at-infinity rigidity -/

namespace Preiss
variable {n m : ℕ}

noncomputable def rigidityError (V : Plane m n) (b : V.1ᗮ)
    (ω : RigidityOmega V) (A : RigidityAdjustedForm V) (z : Euclidean n) : ℝ :=
  A (V.1.orthogonalProjectionOnto z) (V.1.orthogonalProjectionOnto z) +
    inner ℝ (ω (V.1.orthogonalProjectionOnto z) (V.1.orthogonalProjectionOnto z) :
      Euclidean n) (z - proj V z - (b : Euclidean n))

end Preiss
