module
public import Preiss.Analysis.GaussianDerivatives
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

/-! # Gaussian moments of linear projections

The real Gaussian MGF gives all even moments, including zero variance. Linear
projection transfers the formula to a standard Gaussian on any finite dimensional
real inner product space. Polarization gives the fourth moment identities.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace Preiss

theorem integral_gaussianReal_zero_pow_even (v : ℝ≥0) (j : ℕ) :
    (∫ x : ℝ, x ^ (2 * j) ∂gaussianReal 0 v) =
      ((2 * j).factorial : ℝ) / (2 ^ j * (j.factorial : ℝ)) * (v : ℝ) ^ j := by
  have hzero : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 v)) := by simp
  calc
    _ = iteratedDeriv (2 * j) (mgf id (gaussianReal 0 v)) 0 := by
      simpa only [Pi.pow_apply, id_eq] using (iteratedDeriv_mgf_zero hzero (2 * j)).symm
    _ = _ := by
      rw [mgf_id_gaussianReal]
      simpa only [zero_mul, zero_add] using iteratedDeriv_exp_quadratic_even (v : ℝ) j

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_integral_inner_pow_even (y : E) (j : ℕ) :
    (∫ v, (inner ℝ y v) ^ (2 * j) ∂stdGaussian E) =
      ((2 * j).factorial : ℝ) / (2 ^ j * (j.factorial : ℝ)) * ‖y‖ ^ (2 * j) := by
  let L : E →L[ℝ] ℝ := innerSL ℝ y
  have hmean : (∫ v, L v ∂stdGaussian E) = 0 := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id, integral_id_stdGaussian, map_zero]
  have hmap : (stdGaussian E).map L = gaussianReal 0 (‖y‖ ^ 2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, hmean, variance_dual_stdGaussian]
    simp only [L, innerSL_apply_norm]
  calc
    (∫ v, (inner ℝ y v) ^ (2 * j) ∂stdGaussian E) =
        ∫ t : ℝ, t ^ (2 * j) ∂(stdGaussian E).map L := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [hmap, integral_gaussianReal_zero_pow_even]
      simp only [Real.coe_toNNReal _ (sq_nonneg _), ← pow_mul]

theorem integrable_gaussian_inner_pow (y : E) (k : ℕ) :
    Integrable (fun v => (inner ℝ y v) ^ k) (stdGaussian E) := by
  have hLp : MemLp (fun v => inner ℝ y v) (k : ℝ≥0∞) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (k : ℝ≥0∞) (by simp)).const_inner y
  apply hLp.integrable_norm_pow'.mono' (by fun_prop)
  filter_upwards [] with v
  simp only [norm_pow, le_refl]

theorem gaussian_integral_inner_sq_mul_inner_sq (y z : E) :
    (∫ v, (inner ℝ y v) ^ 2 * (inner ℝ z v) ^ 2 ∂stdGaussian E) =
      ‖y‖ ^ 2 * ‖z‖ ^ 2 + 2 * (inner ℝ y z) ^ 2 := by
  have hi (u : E) : Integrable (fun v => (inner ℝ u v) ^ 4) (stdGaussian E) :=
    integrable_gaussian_inner_pow u 4
  have hfour (u : E) : (∫ v, (inner ℝ u v) ^ 4 ∂stdGaussian E) = 3 * ‖u‖ ^ 4 := by
    convert gaussian_integral_inner_pow_even u 2 using 1 <;> norm_num
  calc
    _ = ∫ v, (((inner ℝ (y + z) v) ^ 4 + (inner ℝ (y - z) v) ^ 4 -
      2 * (inner ℝ y v) ^ 4 - 2 * (inner ℝ z v) ^ 4) / 12) ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [inner_add_left, inner_sub_left]
      ring
    _ = (3 * ‖y + z‖ ^ 4 + 3 * ‖y - z‖ ^ 4 - 2 * (3 * ‖y‖ ^ 4) -
        2 * (3 * ‖z‖ ^ 4)) / 12 := by
      have hs : Integrable (fun v => (inner ℝ (y+z) v)^4 + (inner ℝ (y-z) v)^4)
          (stdGaussian E) := (hi (y+z)).fun_add (hi (y-z))
      have hd : Integrable (fun v => (inner ℝ (y+z) v)^4 + (inner ℝ (y-z) v)^4 -
          2 * (inner ℝ y v)^4) (stdGaussian E) := hs.sub' ((hi y).const_mul 2)
      rw [integral_div, integral_sub hd ((hi z).const_mul 2),
        integral_sub hs ((hi y).const_mul 2),
        integral_add (hi (y + z)) (hi (y - z)), integral_const_mul, integral_const_mul]
      rw [hfour, hfour, hfour, hfour]
    _ = _ := by
      simp only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, norm_add_sq_real, norm_sub_sq_real]
      ring

theorem integrable_gaussian_inner_prod {ι : Type*} [Fintype ι] (u : ι → E) :
    Integrable (fun v => ∏ i, inner ℝ (u i) v) (stdGaussian E) := by
  have hn : Integrable (fun v : E => ‖v‖ ^ Fintype.card ι) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (Fintype.card ι) (by simp)).integrable_norm_pow'
  apply (hn.const_mul (∏ i, ‖u i‖)).mono' (by fun_prop)
  filter_upwards [] with v
  calc
    ‖∏ i, inner ℝ (u i) v‖ = ∏ i, ‖inner ℝ (u i) v‖ := norm_prod _ _
    _ ≤ ∏ i, (‖u i‖ * ‖v‖) := Finset.prod_le_prod₀
      (fun i _ => norm_nonneg _) (fun i _ => norm_inner_le_norm _ _)
    _ = (∏ i, ‖u i‖) * ‖v‖ ^ Fintype.card ι := by simp [Finset.prod_mul_distrib]

theorem integrable_gaussian_four_inner (a b c d : E) :
    Integrable (fun v => inner ℝ a v * inner ℝ b v * inner ℝ c v * inner ℝ d v)
      (stdGaussian E) := by
  simpa [Fin.prod_univ_four] using integrable_gaussian_inner_prod ![a,b,c,d]

theorem gaussian_integral_four_inner (a b c d : E) :
    (∫ v, inner ℝ a v * inner ℝ b v * inner ℝ c v * inner ℝ d v ∂stdGaussian E) =
      inner ℝ a b * inner ℝ c d + inner ℝ a c * inner ℝ b d +
        inner ℝ a d * inner ℝ b c := by
  have hi (u w : E) : Integrable (fun v => (inner ℝ u v)^2 * (inner ℝ w v)^2)
      (stdGaussian E) := by
    convert integrable_gaussian_four_inner u u w w using 1
    funext v
    ring
  calc
    _ = ∫ v, (((inner ℝ (a+b) v)^2 * (inner ℝ (c+d) v)^2 -
      (inner ℝ (a+b) v)^2 * (inner ℝ (c-d) v)^2 -
      (inner ℝ (a-b) v)^2 * (inner ℝ (c+d) v)^2 +
      (inner ℝ (a-b) v)^2 * (inner ℝ (c-d) v)^2) / 16) ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [inner_add_left, inner_sub_left]
      ring
    _ = ((‖a+b‖^2 * ‖c+d‖^2 + 2 * (inner ℝ (a+b) (c+d))^2) -
      (‖a+b‖^2 * ‖c-d‖^2 + 2 * (inner ℝ (a+b) (c-d))^2) -
      (‖a-b‖^2 * ‖c+d‖^2 + 2 * (inner ℝ (a-b) (c+d))^2) +
      (‖a-b‖^2 * ‖c-d‖^2 + 2 * (inner ℝ (a-b) (c-d))^2)) / 16 := by
      have hd : Integrable (fun v => (inner ℝ (a+b) v)^2 * (inner ℝ (c+d) v)^2 -
          (inner ℝ (a+b) v)^2 * (inner ℝ (c-d) v)^2) (stdGaussian E) := (hi (a+b) (c+d)).sub' (hi (a+b) (c-d))
      have hdd : Integrable (fun v => (inner ℝ (a+b) v)^2 * (inner ℝ (c+d) v)^2 -
          (inner ℝ (a+b) v)^2 * (inner ℝ (c-d) v)^2 -
          (inner ℝ (a-b) v)^2 * (inner ℝ (c+d) v)^2) (stdGaussian E) := hd.sub' (hi (a-b) (c+d))
      rw [integral_div, integral_add hdd (hi (a-b) (c-d)),
        integral_sub hd (hi (a-b) (c+d)),
        integral_sub (hi (a+b) (c+d)) (hi (a+b) (c-d))]
      rw [gaussian_integral_inner_sq_mul_inner_sq,
        gaussian_integral_inner_sq_mul_inner_sq,
        gaussian_integral_inner_sq_mul_inner_sq,
        gaussian_integral_inner_sq_mul_inner_sq]
    _ = _ := by
      simp only [norm_add_sq_real, norm_sub_sq_real, inner_add_left, inner_sub_left,
        inner_add_right, inner_sub_right]
      ring

end Preiss
