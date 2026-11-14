import Preiss.Uniform.FlatAtInfinity.TraceData
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Tactic

namespace Preiss
variable {n m : ℕ}

theorem exists_rigidity_forms_of_symmetry
    (B : MomentCoefficientFamily n) (V : Plane m n) (b : V.1ᗮ)
    (h₃ : ∀ u v w : Euclidean n, B 3 2 ![u,v,w] = B 3 2 ![v,u,w])
    (h₂ : ∀ u v : Euclidean n, B 2 2 ![u,v] = B 2 2 ![v,u]) :
    ∃ ω : RigidityOmega V, IsRigidityOmega B V b ω ∧
      ∃ A : RigidityAdjustedForm V, IsRigidityAdjustedForm B V b ω A := by
  classical
  let R : (Euclidean n →L[ℝ] ℝ) →L[ℝ] V.1ᗮ :=
    (InnerProductSpace.toDual ℝ V.1ᗮ).symm.toContinuousLinearEquiv.toContinuousLinearMap |>.comp
      ((ContinuousLinearMap.compL ℝ V.1ᗮ (Euclidean n) ℝ).flip V.1ᗮ.subtypeL)
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V.1) V.1ᗮ :=
    R.compContinuousMultilinearMap
      ((B 3 2).curryRight.compContinuousLinearMap (fun _ => V.1.subtypeL))
  let C : RigidityOmega V :=
    (continuousMultilinearCurryFin1 ℝ V.1 V.1ᗮ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      T.curryLeft
  have hC (u v : V.1) (w : V.1ᗮ) :
      inner ℝ (C u v) w = B 3 2 ![(u : Euclidean n),(v : Euclidean n),(w : Euclidean n)] := by
    change inner ℝ ((InnerProductSpace.toDual ℝ V.1ᗮ).symm _) w = _
    rw [InnerProductSpace.toDual_symm_apply]
    change B 3 2 _ = B 3 2 _
    congr 1
    ext i
    fin_cases i <;> rfl
  let J : ℝ →L[ℝ] V.1ᗮ := ContinuousLinearMap.toSpanSingleton ℝ b
  let D : RigidityOmega V :=
    ((ContinuousLinearMap.compL ℝ V.1 ℝ V.1ᗮ) J).comp (innerSL ℝ)
  let ω : RigidityOmega V := (3 : ℝ) • C - (4 : ℝ) • D
  have hω (u v : V.1) (w : V.1ᗮ) :
      inner ℝ (ω u v) w =
        3 * B 3 2 ![(u : Euclidean n),(v : Euclidean n),(w : Euclidean n)] -
          4 * inner ℝ u v * inner ℝ b w := by
    change inner ℝ ((3 : ℝ) • C u v - (4 : ℝ) • ((inner ℝ u v) • b)) w = _
    simp only [inner_sub_left, real_inner_smul_left, hC]
    ring
  have hsym (u v : V.1) : ω u v = ω v u := by
    apply ext_inner_right ℝ
    intro w
    rw [hω, hω, h₃, real_inner_comm v u]
  let P : RigidityAdjustedForm V :=
    (continuousMultilinearCurryFin1 ℝ V.1 ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((B 2 2).compContinuousLinearMap (fun _ => V.1.subtypeL)).curryLeft
  have hP (u v : V.1) : P u v = B 2 2 ![(u : Euclidean n),(v : Euclidean n)] := by
    change B 2 2 _ = B 2 2 _
    congr 1
    ext i
    fin_cases i <;> rfl
  let A : RigidityAdjustedForm V := P +
    ((ContinuousLinearMap.compL ℝ V.1 V.1ᗮ ℝ) (innerSL ℝ b)).comp ω
  have hA (u v : V.1) : A u v =
      B 2 2 ![(u : Euclidean n),(v : Euclidean n)] + inner ℝ (ω u v) b := by
    change P u v + inner ℝ b (ω u v) = _
    rw [hP, real_inner_comm b]
  refine ⟨ω, ⟨hsym, hω⟩, A, ?_, hA⟩
  intro u v
  rw [hA, hA, h₂, hsym]

#print axioms exists_rigidity_forms_of_symmetry

theorem exists_rigidityOmega_and_adjustedForm_proved
    (μ : MeasureTheory.Measure (Euclidean n)) (hm : 0 < m) (hμ : IsUnitUniform m μ)
    (B : MomentCoefficientFamily n) (hB : IsMomentExpansion μ B)
    (V : Plane m n) (hV : IsTangentAtInfinity m μ (unitFlat V))
    (b : V.1ᗮ) (hb : IsFirstMomentNormalVector B V b) :
    ∃ ω : RigidityOmega V, IsRigidityOmega B V b ω ∧
      ∃ A : RigidityAdjustedForm V, IsRigidityAdjustedForm B V b ω A := by
  apply exists_rigidity_forms_of_symmetry B V b
  · intro u v w
    have h := hB.1 3 2 (Equiv.swap 0 1) ![u,v,w]
    have heq : ![u,v,w] ∘ Equiv.swap (0 : Fin 3) 1 = ![v,u,w] := by
      funext i
      fin_cases i <;> simp [Function.comp_def, Equiv.swap_apply_def]
    rw [heq] at h
    exact h.symm
  · intro u v
    have h := hB.1 2 2 (Equiv.swap 0 1) ![u,v]
    have heq : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
      funext i
      fin_cases i <;> simp [Function.comp_def, Equiv.swap_apply_def]
    rw [heq] at h
    exact h.symm

#print axioms exists_rigidityOmega_and_adjustedForm_proved
end Preiss
