module
public import Preiss.Analysis.GradedProjection
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.LinearAlgebra.Projection

@[expose] public section
namespace Preiss
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}

section Approximation
open Filter Set
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem functional_comp_projection_eq_self (V W : Submodule ℝ E) (hc : IsCompl V W)
    (Q : E →L[ℝ] E) (hfix : ∀ v ∈ V, Q v = v) (hkill : ∀ w ∈ W, Q w = 0)
    (f : E →L[ℝ] F) (hf : ∀ w ∈ W, f w = 0) : f.comp Q = f := by
  ext x
  obtain ⟨v,w,hvw,_⟩ := Submodule.existsUnique_add_of_isCompl hc x
  change f (Q x) = f x
  rw [← hvw, map_add Q, hfix v v.property, hkill w w.property, add_zero,
    map_add f, hf w w.property, add_zero]

theorem exists_analyticApproximation_of_weightedComplement
    (P : Fin N → E →L[ℝ] E) (hP : IsOrthogonalGrading P) (V : Submodule ℝ E)
    (f g : ℝ → E →L[ℝ] F) (hg : AnalyticAt ℝ g 0) (hg0 : g 0 = 0)
    (r : ℝ → ℝ)
    (hvanish : ∀ s : ℝ, 0 < s → ∀ w ∈ weightedComplement P V s, f s w = 0)
    (herr : Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun s => (f s - g s).comp V.subtypeL) r) :
    ∃ a : ℝ → E →L[ℝ] F, AnalyticAt ℝ a 0 ∧ a 0 = 0 ∧
      Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0)) (fun s => f s - a s) r := by
  obtain ⟨Q,hQa,hQ⟩ := analyticAt_weightedProjection_zero P hP V
  let S : ℝ → E →L[ℝ] V := fun s => V.orthogonalProjectionOnto.comp (Q s)
  let a : ℝ → E →L[ℝ] F := fun s => (g s).comp (Q s)
  have ha : AnalyticAt ℝ a 0 :=
    ((ContinuousLinearMap.compL ℝ E E F).analyticAt_bilinear _).comp₂ hg hQa
  have hSa : AnalyticAt ℝ S 0 :=
    ((ContinuousLinearMap.compL ℝ E E V).analyticAt_bilinear _).comp₂ analyticAt_const hQa
  have hSb : Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0)) S (fun _ => (1 : ℝ)) :=
    (hSa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  let A : ℝ → V →L[ℝ] F := fun s => (f s - g s).comp V.subtypeL
  have hnormcomp : Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun s => (A s).comp (S s)) (fun s => ‖A s‖ * ‖S s‖) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with s
    calc
      ‖(A s).comp (S s)‖ ≤ ‖A s‖ * ‖S s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = 1 * ‖‖A s‖ * ‖S s‖‖ := by
        rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg (A s)) (norm_nonneg (S s)))]
  have hprod : Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun s => ‖A s‖ * ‖S s‖) r := by
    have hAn : Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0)) (fun s => ‖A s‖) r :=
      Asymptotics.IsBigO.norm_left (f' := A) (g := r) herr
    have hSn : Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0)) (fun s => ‖S s‖)
        (fun _ => (1 : ℝ)) := Asymptotics.IsBigO.norm_left (f' := S) hSb
    simpa only [mul_one] using hAn.mul hSn
  have herror := hnormcomp.trans hprod
  have heq : (fun s => (A s).comp (S s)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun s => f s - a s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨hc,hm,hfix,hkill⟩ := hQ s hs
    have hcomp := functional_comp_projection_eq_self V (weightedComplement P V s)
      hc (Q s) hfix hkill (f s) (hvanish s hs)
    ext x
    have hSx : ((S s x : V) : E) = Q s x :=
      Submodule.starProjection_eq_self_iff.mpr (hm x)
    change (f s - g s) ((S s x : V) : E) = (f s - (g s).comp (Q s)) x
    rw [hSx]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    have hfQ : f s (Q s x) = f s x := congrArg (fun T : E →L[ℝ] F => T x) hcomp
    rw [hfQ]
  refine ⟨a,ha,?_,herror.congr' heq (Filter.EventuallyEq.refl _ _)⟩
  ext x
  simp only [a,hg0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply]
end Approximation

end Preiss
