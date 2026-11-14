import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open MeasureTheory Filter
open scoped Topology
namespace Preiss

theorem tendsto_weighted_integral_mul_of_square_limits
    {X I : Type*} [MeasurableSpace X] (μ : Measure X) (l : Filter I)
    (weight : I → X → ℝ) (scale : I → ℝ) (f g h : X → ℝ)
    (hints : ∀ᶠ i in l,
      Integrable (fun x => weight i x * (f x + g x)^2 * h x) μ ∧
      Integrable (fun x => weight i x * (f x)^2 * h x) μ ∧
      Integrable (fun x => weight i x * (g x)^2 * h x) μ)
    (a b c : ℝ)
    (ha : Tendsto (fun i => scale i * ∫ x, weight i x * (f x + g x)^2 * h x ∂μ) l (𝓝 a))
    (hb : Tendsto (fun i => scale i * ∫ x, weight i x * (f x)^2 * h x ∂μ) l (𝓝 b))
    (hc : Tendsto (fun i => scale i * ∫ x, weight i x * (g x)^2 * h x ∂μ) l (𝓝 c)) :
    Tendsto (fun i => scale i * ∫ x, weight i x * f x * g x * h x ∂μ)
      l (𝓝 ((a-b-c)/2)) := by
  have ht := ((ha.sub hb).sub hc).div_const 2
  apply ht.congr'
  filter_upwards [hints] with i hi
  have hfun : (fun x => weight i x * f x * g x * h x) =
      (fun x => (1/2 : ℝ) * ((weight i x * (f x+g x)^2 * h x -
        weight i x * (f x)^2 * h x) - weight i x * (g x)^2 * h x)) := by
    funext x
    ring
  rw [hfun, integral_const_mul, integral_sub (hi.1.sub hi.2.1) hi.2.2,
    integral_sub hi.1 hi.2.1]
  ring

theorem integrable_weighted_mul_of_squares
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (weight f g h : X → ℝ)
    (hsum : Integrable (fun x => weight x * (f x+g x)^2 * h x) μ)
    (hf : Integrable (fun x => weight x * (f x)^2 * h x) μ)
    (hg : Integrable (fun x => weight x * (g x)^2 * h x) μ) :
    Integrable (fun x => weight x * f x * g x * h x) μ := by
  have hh := ((hsum.sub hf).sub hg).const_mul (1/2 : ℝ)
  convert hh using 1
  funext x
  ring

theorem tendsto_weighted_bilinear_mixed_of_diagonal_limits
    {X I E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (μ : Measure X) (l : Filter I) (weight : I → X → ℝ) (scale : I → ℝ)
    (p : X → E) (q : X → F) (A : E →L[ℝ] E →L[ℝ] F)
    (hsymm : ∀ u v, A u v = A v u)
    (hint : ∀ u w, ∀ᶠ i in l,
      Integrable (fun x => weight i x * (inner ℝ (p x) u)^2 * inner ℝ (q x) w) μ)
    (hlim : ∀ u w, Tendsto (fun i => scale i *
      ∫ x, weight i x * (inner ℝ (p x) u)^2 * inner ℝ (q x) w ∂μ)
      l (𝓝 (inner ℝ (A u u) w / 8)))
    (u v : E) (w : F) :
    Tendsto (fun i => scale i *
      ∫ x, weight i x * inner ℝ (p x) u * inner ℝ (p x) v * inner ℝ (q x) w ∂μ)
      l (𝓝 (inner ℝ (A u v) w / 8)) := by
  have hs : ∀ᶠ i in l,
      Integrable (fun x => weight i x * (inner ℝ (p x) u + inner ℝ (p x) v)^2 *
        inner ℝ (q x) w) μ ∧
      Integrable (fun x => weight i x * (inner ℝ (p x) u)^2 * inner ℝ (q x) w) μ ∧
      Integrable (fun x => weight i x * (inner ℝ (p x) v)^2 * inner ℝ (q x) w) μ := by
    filter_upwards [hint (u+v) w, hint u w, hint v w] with i hi hu hv
    exact ⟨by simpa only [inner_add_right] using hi, hu, hv⟩
  have hsum := hlim (u+v) w
  simp only [inner_add_right] at hsum
  have ht := tendsto_weighted_integral_mul_of_square_limits μ l weight scale
    (fun x => inner ℝ (p x) u) (fun x => inner ℝ (p x) v) (fun x => inner ℝ (q x) w)
    hs _ _ _ hsum (hlim u w) (hlim v w)
  convert ht using 1
  congr 1
  simp only [map_add, ContinuousLinearMap.add_apply, inner_add_left, hsymm v u]
  ring

end Preiss

#print axioms Preiss.tendsto_weighted_integral_mul_of_square_limits
#print axioms Preiss.integrable_weighted_mul_of_squares
#print axioms Preiss.tendsto_weighted_bilinear_mixed_of_diagonal_limits
