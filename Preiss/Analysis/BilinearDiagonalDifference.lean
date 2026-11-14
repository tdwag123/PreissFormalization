module
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Tactic

@[expose] public section
namespace Preiss

theorem norm_bilinear_diagonal_sub_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E →L[ℝ] E →L[ℝ] F) (z p : E) :
    ‖Q z z - Q p p‖ ≤ ‖Q‖ * ‖z-p‖ * (‖z‖+‖p‖) := by
  have heq : Q z z - Q p p = Q (z-p) z + Q p (z-p) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  calc
    _ ≤ ‖Q (z-p) z‖ + ‖Q p (z-p)‖ := norm_add_le _ _
    _ ≤ ‖Q‖ * ‖z-p‖ * ‖z‖ + ‖Q‖ * ‖p‖ * ‖z-p‖ :=
      add_le_add (Q.le_opNorm₂ (z-p) z) (Q.le_opNorm₂ p (z-p))
    _ = _ := by ring

end Preiss
