module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Asymptotics
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section
open Filter Asymptotics
namespace Preiss
variable {α E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [SeminormedAddCommGroup G]

theorem isBigO_continuousLinearMap_iff_forall_apply (l : Filter α)
    (T : α → E →L[ℝ] F) (g : α → G) :
    IsBigO l T g ↔ ∀ v : E, IsBigO l (fun t => T t v) g := by
  classical
  constructor
  · intro h v
    simpa only [ContinuousLinearMap.apply_apply] using
      ((ContinuousLinearMap.apply ℝ F v).isBigO_comp T l).trans h
  · intro h
    let b := Module.finBasis ℝ E
    let U : α → Fin (Module.finrank ℝ E) → F := fun t i => T t (b i)
    have hU : IsBigO l U g := isBigO_pi.mpr (fun i => h (b i))
    have hT : IsBigO l T U := by
      apply IsBigO.of_bound (Fintype.card (Fin (Module.finrank ℝ E)) •
        ‖b.equivFunL.toContinuousLinearMap‖)
      apply Filter.Eventually.of_forall
      intro t
      exact b.opNorm_le (norm_nonneg (U t)) (fun i => norm_le_pi_norm (U t) i)
    exact hT.trans hU

theorem isBigO_restrict_span_of_forall_mem (l : Filter α)
    (T : α → E →L[ℝ] F) (g : α → G) (S : Set E)
    (h : ∀ v ∈ S, IsBigO l (fun t => T t v) g) :
    IsBigO l (fun t => (T t).comp (Submodule.span ℝ S).subtypeL) g := by
  apply (isBigO_continuousLinearMap_iff_forall_apply _ _ _).mpr
  intro v
  change IsBigO l (fun t => T t (v : E)) g
  refine Submodule.span_induction (p := fun x _ => IsBigO l (fun t => T t x) g)
    (fun x hx => h x hx) ?_ ?_ ?_ v.property
  · simpa only [map_zero] using (isBigO_zero g l : IsBigO l (fun _ : α => (0 : F)) g)
  · intro x y hx hy hX hY
    simpa only [map_add] using hX.add hY
  · intro a x hx hX
    have H := ((a • ContinuousLinearMap.id ℝ F).isBigO_comp (fun t => T t x) l).trans hX
    simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul] using H

end Preiss
