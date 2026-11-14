module
public import Preiss.Analysis.GaussianWeight
public import Preiss.Analysis.MomentDetermination

@[expose] public section

/-! # Determination by Gaussian weighted polynomial moments

Weight each measure by the positive Gaussian. Polynomial growth makes the weighted
measures finite and gives every exponential moment of each linear projection.
Moment determinacy identifies their characteristic functions; cancellation of the
strictly positive finite weight identifies the original measures.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace Preiss

theorem measure_eq_of_gaussian_polynomial_moments_eq {n : ℕ}
    (μ ν : Measure (Euclidean n)) (hμ : μ.Regular) (hν : ν.Regular)
    (C p : ℝ) (hμgrowth : HasPolynomialGrowthBound μ C p)
    (hνgrowth : HasPolynomialGrowthBound ν C p)
    (heq : ∀ P : MvPolynomial (Fin n) ℝ,
      (∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖ ^ 2) ∂μ) =
      ∫ z, MvPolynomial.eval (fun j => z j) P * Real.exp (-‖z‖ ^ 2) ∂ν) : μ = ν := by
  classical
  let a : Euclidean n → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2))
  let ρ := μ.withDensity a
  let σ := ν.withDensity a
  have ha : Measurable a := by dsimp [a]; fun_prop
  have ha_pos (z : Euclidean n) : a z ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have ha_top (z : Euclidean n) : a z ≠ ∞ := ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_gaussian μ C p hμgrowth
  letI : IsFiniteMeasure σ := isFiniteMeasure_withDensity_gaussian ν C p hνgrowth
  have hmom (P : MvPolynomial (Fin n) ℝ) :
      (∫ z, MvPolynomial.eval (fun j => z j) P ∂ρ) =
      ∫ z, MvPolynomial.eval (fun j => z j) P ∂σ := by
    change (∫ z, MvPolynomial.eval (fun j => z j) P ∂μ.withDensity a) =
      ∫ z, MvPolynomial.eval (fun j => z j) P ∂ν.withDensity a
    rw [integral_withDensity_eq_integral_toReal_smul ha
        (Filter.Eventually.of_forall fun z => (ha_top z).lt_top),
      integral_withDensity_eq_integral_toReal_smul ha
        (Filter.Eventually.of_forall fun z => (ha_top z).lt_top)]
    simp only [a, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    simpa only [mul_comm] using heq P
  have hweighted : ρ = σ := by
    apply Measure.ext_of_charFun
    funext v
    have hproj (k : ℕ) : (∫ z, (inner ℝ z v) ^ k ∂ρ) =
        ∫ z, (inner ℝ z v) ^ k ∂σ := by
      let P : MvPolynomial (Fin n) ℝ :=
        (∑ i : Fin n, MvPolynomial.C (v i) * MvPolynomial.X i) ^ k
      have heval (z : Euclidean n) : MvPolynomial.eval (fun j => z j) P = (inner ℝ z v) ^ k := by
        dsimp [P]
        rw [MvPolynomial.eval_pow]
        congr 1
        change MvPolynomial.eval (fun j => z j)
          (∑ i : Fin n, MvPolynomial.C (v i) * MvPolynomial.X i) = ∑ i : Fin n, v i * z i
        simp
      simpa only [heval] using hmom P
    have H := complexMGF_eq_of_all_moments_eq ρ σ (fun z => inner ℝ z v) (fun z => inner ℝ z v)
      (fun t => integrable_exp_inner_withDensity_gaussian μ C p hμgrowth v t)
      (fun t => integrable_exp_inner_withDensity_gaussian ν C p hνgrowth v t) hproj
    simpa only [complexMGF, charFun_apply, mul_comm] using congrFun H Complex.I
  have hcancelμ : ρ.withDensity (fun z => (a z)⁻¹) = μ :=
    withDensity_inv_same ha (Filter.Eventually.of_forall ha_pos) (Filter.Eventually.of_forall ha_top)
  have hcancelν : σ.withDensity (fun z => (a z)⁻¹) = ν :=
    withDensity_inv_same ha (Filter.Eventually.of_forall ha_pos) (Filter.Eventually.of_forall ha_top)
  calc
    μ = ρ.withDensity (fun z => (a z)⁻¹) := hcancelμ.symm
    _ = σ.withDensity (fun z => (a z)⁻¹) := congrArg (fun η => η.withDensity (fun z => (a z)⁻¹)) hweighted
    _ = ν := hcancelν

end Preiss
