module
public import Preiss.Uniform.Defs
public import Preiss.Uniform.Homogeneous
public import Preiss.Analysis.GaussianBallPower
public import Preiss.Geometry.PlaneMeasure
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace Preiss
variable {n m : ℕ}

theorem uniform_radial_pushforward (μ : Measure (Euclidean n))
    (hm : 0 < m) (hμ : IsUnitUniform m μ) (y : Euclidean n) (hy : y ∈ μ.support)
    (V : Plane m n) :
    μ.map (fun z => ‖z - y‖) = (unitFlat V).map (fun z => ‖z‖) := by
  letI : μ.Regular := hμ.1
  have hnorm : Measurable (fun z : Euclidean n => ‖z‖) := continuous_norm.measurable
  have hdist : Measurable (fun z : Euclidean n => ‖z - y‖) :=
    (continuous_id.sub continuous_const).norm.measurable
  have hzero (ρ : Measure (Euclidean n)) (x : Euclidean n)
      (hball : ∀ t : ℝ, 0 < t → ρ (closedBall x t) = ENNReal.ofReal (t ^ m)) :
      ρ (closedBall x 0) = 0 := by
    have hlim₀ : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ m)) (𝓝 0)
        (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ m))) :=
      (ENNReal.continuous_ofReal.comp (continuous_pow m)).continuousAt.tendsto
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ m))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_pow hm.ne', ENNReal.ofReal_zero] using
        hlim₀.mono_left nhdsWithin_le_nhds
    apply le_antisymm _ bot_le
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hball t ht]
    exact measure_mono (closedBall_subset_closedBall ht.le)
  let ρ := μ.map (fun z => ‖z - y‖)
  let σ := (unitFlat V).map (fun z => ‖z‖)
  have hρ (t : ℝ) : ρ (Iic t) = μ (closedBall y t) := by
    rw [Measure.map_apply hdist measurableSet_Iic]
    rfl
  have hσ (t : ℝ) : σ (Iic t) = unitFlat V (closedBall 0 t) := by
    rw [Measure.map_apply hnorm measurableSet_Iic]
    congr 1
    ext z
    simp only [mem_preimage, mem_Iic, mem_closedBall, dist_zero_right]
  have heq (t : ℝ) : ρ (Iic t) = σ (Iic t) := by
    rw [hρ, hσ]
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [closedBall_eq_empty.mpr ht, closedBall_eq_empty.mpr ht]
      simp only [measure_empty]
    · rw [hzero μ y (fun t ht => hμ.2.2 y hy t ht),
        hzero (unitFlat V) 0 (fun t ht => unitFlat_closedBall V 0 V.1.zero_mem ht)]
    · rw [hμ.2.2 y hy t ht, unitFlat_closedBall V 0 V.1.zero_mem ht]
  have hfinite (t : ℝ) : ρ (Iic t) ≠ ∞ := by
    rw [hρ]
    exact (isCompact_closedBall y t).measure_lt_top.ne
  apply Measure.ext_of_Ioc' ρ σ
  · intro a b hab
    exact ne_top_of_le_ne_top (hfinite b) (measure_mono Ioc_subset_Iic_self)
  · intro a b hab
    have hσfinite : σ (Iic a) ≠ ∞ := by rw [← heq]; exact hfinite a
    rw [← Iic_sdiff_Iic,
      measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet (hfinite a),
      measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet hσfinite,
      heq a, heq b]

theorem integral_gaussian_mul_homogeneous
    (μ : Measure (Euclidean n)) (hμ : μ.Regular) (hcone : IsConical m μ)
    (h : Euclidean n → ℝ) (hh : Measurable h) (hnonneg : ∀ z, 0 ≤ h z)
    (a : ℝ) (ha : 0 < (m : ℝ) + a)
    (hhom : ∀ r > 0, ∀ z, h (r • z) = r ^ a * h z)
    (hint : IntegrableOn h (closedBall 0 1) μ) :
    Integrable (fun z => Real.exp (-‖z‖ ^ 2) * h z) μ ∧
    (∫ z, Real.exp (-‖z‖ ^ 2) * h z ∂μ) =
      Real.Gamma (((m : ℝ) + a) / 2 + 1) * ∫ z in closedBall 0 1, h z ∂μ := by
  letI : μ.Regular := hμ
  let ρ : Measure (Euclidean n) := μ.withDensity (fun z => ENNReal.ofReal (h z))
  let C : ℝ := ∫ z in closedBall 0 1, h z ∂μ
  have hC : 0 ≤ C := integral_nonneg hnonneg
  have hball (r : ℝ) (hr : 0 < r) :
      ρ (closedBall 0 r) = ENNReal.ofReal (C * r ^ ((m : ℝ) + a)) := by
    have hint_r := integrableOn_homogeneous_closedBall μ hcone h hh a hhom hint r hr
    rw [withDensity_apply _ measurableSet_closedBall,
      ← ofReal_integral_eq_lintegral_ofReal hint_r (ae_of_all _ hnonneg),
      integral_homogeneous_closedBall μ hcone h hh a hhom r hr]
    exact congrArg ENNReal.ofReal (mul_comm _ _)
  obtain ⟨hintρ, hvalρ⟩ := integral_gaussian_of_closedBall_power ρ C ((m : ℝ) + a) hC ha hball
  have hw : Measurable (fun z => ENNReal.ofReal (h z)) := ENNReal.measurable_ofReal.comp hh
  have hwfinite : ∀ᵐ z ∂μ, ENNReal.ofReal (h z) < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hprod : (fun z => (ENNReal.ofReal (h z)).toReal • Real.exp (-‖z‖ ^ 2)) =
      (fun z => Real.exp (-‖z‖ ^ 2) * h z) := by
    funext z
    rw [ENNReal.toReal_ofReal (hnonneg z), smul_eq_mul, mul_comm]
  have hintμ := (integrable_withDensity_iff_integrable_smul' hw hwfinite).mp hintρ
  rw [hprod] at hintμ
  have hval := integral_withDensity_eq_integral_toReal_smul hw hwfinite
    (fun z => Real.exp (-‖z‖ ^ 2))
  rw [hprod] at hval
  exact ⟨hintμ, hval.symm.trans hvalρ⟩

end Preiss
