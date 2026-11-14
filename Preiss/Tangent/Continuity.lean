import Preiss.Tangent.Blowup
import Preiss.Analysis.Vague.CompactTests
import FormalizingGMT.WeakConvergence.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open MeasureTheory Filter Set
open scoped Topology CompactlySupported
namespace Preiss
variable {n m : ℕ}

theorem vague_smul_map_sub_div (μ : ℕ → Measure (Euclidean n))
    (ν : Measure (Euclidean n)) (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (a : ℕ → Euclidean n) (b : Euclidean n) (ha : Tendsto a atTop (𝓝 b))
    (r : ℕ → ℝ) (s : ℝ) (hr : ∀ i, 0 < r i) (hs : 0 < s)
    (hrs : Tendsto r atTop (𝓝 s)) (c : ℕ → ℝ) (d : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : 0 ≤ d) (hcd : Tendsto c atTop (𝓝 d)) :
    Measure.WeaklyConverges
      (fun i => ENNReal.ofReal (c i) • (μ i).map (fun z => (r i)⁻¹ • (z - a i)))
      (ENNReal.ofReal d • ν.map (fun z => s⁻¹ • (z - b))) := by
  intro f
  -- The convergent parameter sequence together with its limit is compact. Its
  -- image of the support of `f` supplies one common compact support for all tests.
  let P : Set (Euclidean n × ℝ) := insert (b, s) (range (fun i => (a i, r i)))
  have hP : IsCompact P := (ha.prodMk_nhds hrs).isCompact_insert_range
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let p₀ : P := ⟨(b, s), mem_insert _ _⟩
  let p : ℕ → P := fun i => ⟨(a i, r i), mem_insert_of_mem _ (mem_range_self i)⟩
  have hp : Tendsto p atTop (𝓝 p₀) := tendsto_subtype_rng.mpr (ha.prodMk_nhds hrs)
  have hpos (q : P) : 0 < q.val.2 := by
    rcases mem_insert_iff.mp q.property with h | ⟨i, hi⟩
    · simpa only [h] using hs
    · simpa only [← hi] using hr i
  let F (q : P) (z : Euclidean n) := f (q.val.2⁻¹ • (z - q.val.1))
  let T (w : P × Euclidean n) := w.1.val.1 + w.1.val.2 • w.2
  have hT : Continuous T :=
    (continuous_fst.subtype_val.fst).add
      ((continuous_fst.subtype_val.snd).smul continuous_snd)
  let K : Set (Euclidean n) := T '' (univ ×ˢ tsupport f)
  have hK : IsCompact K := (isCompact_univ.prod f.hasCompactSupport).image hT
  have hsupport (q : P) : Function.support (F q) ⊆ K := by
    intro z hz
    refine ⟨(q, q.val.2⁻¹ • (z - q.val.1)),
      ⟨mem_univ _, subset_tsupport f hz⟩, ?_⟩
    simp [T, smul_smul, (hpos q).ne']
  let g (q : P) : C_c(Euclidean n, ℝ) :=
    { toContinuousMap := ⟨F q, f.continuous.comp
        ((continuous_id.sub continuous_const).const_smul q.val.2⁻¹)⟩
      hasCompactSupport' := hK.of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal (hsupport q) hK.isClosed) }
  have hzero (q : P) (z : Euclidean n) (hz : z ∉ K) : g q z = 0 := by
    by_contra h
    exact hz (hsupport q h)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hF : Continuous (fun w : P × K => F w.1 w.2) :=
    f.continuous.comp
      (((continuous_fst.subtype_val.snd).inv₀ (fun w => (hpos w.1).ne')).smul
        (continuous_snd.subtype_val.sub continuous_fst.subtype_val.fst))
  have hunif : ∀ ε > 0, ∀ᶠ i in atTop, ∀ z, |g (p i) z - g p₀ z| < ε := by
    intro ε hε
    have hlocal := Metric.tendstoUniformly_iff.mp
      (Continuous.tendstoUniformly (fun q : P => fun z : K => F q z) hF p₀) ε hε
    filter_upwards [hp.eventually hlocal] with i hi
    intro z
    by_cases hz : z ∈ K
    · change |F (p i) z - F p₀ z| < ε
      calc
        _ = |F p₀ z - F (p i) z| := abs_sub_comm _ _
        _ = dist (F p₀ z) (F (p i) z) := (Real.dist_eq _ _).symm
        _ < ε := hi ⟨z, hz⟩
    · rw [hzero (p i) z hz, hzero p₀ z hz, sub_self, abs_zero]
      exact hε
  have hint := vague_integral_moving_compact_test μ ν hμ hν hlim K hK
    (fun i => g (p i)) (g p₀) (fun i => hzero (p i)) (hzero p₀) hunif
  have hchange (ρ : Measure (Euclidean n)) (q : P) (t : ℝ) (ht : 0 ≤ t) :
      (∫ z, f z ∂(ENNReal.ofReal t • ρ.map
        (fun z => q.val.2⁻¹ • (z - q.val.1)))) = t * ∫ z, g q z ∂ρ := by
    have hφ : Measurable (fun z : Euclidean n => q.val.2⁻¹ • (z - q.val.1)) :=
      ((continuous_id.sub continuous_const).const_smul q.val.2⁻¹).measurable
    have hf : AEStronglyMeasurable (fun z : Euclidean n => f z)
        (ρ.map (fun z => q.val.2⁻¹ • (z - q.val.1))) :=
      f.continuous.aestronglyMeasurable
    have hmap : (∫ z, f z ∂ρ.map (fun z => q.val.2⁻¹ • (z - q.val.1))) =
        ∫ z, g q z ∂ρ := integral_map hφ.aemeasurable hf
    rw [integral_smul_measure, ENNReal.toReal_ofReal ht, smul_eq_mul]
    exact congrArg (fun v : ℝ => t * v) hmap
  have hseq : (fun i => ∫ z, f z ∂(ENNReal.ofReal (c i) •
      (μ i).map (fun z => (r i)⁻¹ • (z - a i)))) =
      (fun i => c i * ∫ z, g (p i) z ∂μ i) := by
    funext i
    exact hchange (μ i) (p i) (c i) (hc i)
  rw [hseq, hchange ν p₀ d hd]
  exact hcd.mul hint

theorem vague_dimensionalBlowup_moving (μ : ℕ → Measure (Euclidean n))
    (ν : Measure (Euclidean n)) (hμ : ∀ i, (μ i).Regular) (hν : ν.Regular)
    (hlim : Measure.WeaklyConverges μ ν)
    (a : ℕ → Euclidean n) (b : Euclidean n) (ha : Tendsto a atTop (𝓝 b))
    (r : ℕ → ℝ) (s : ℝ) (hr : ∀ i, 0 < r i) (hs : 0 < s)
    (hrs : Tendsto r atTop (𝓝 s)) :
    Measure.WeaklyConverges (fun i => dimensionalBlowup m (μ i) (a i) (r i))
      (dimensionalBlowup m ν b s) := by
  have hcoeff : Tendsto (fun i => ((r i) ^ m)⁻¹) atTop (𝓝 ((s ^ m)⁻¹)) :=
    (hrs.pow m).inv₀ (pow_pos hs m).ne'
  have hconv := vague_smul_map_sub_div μ ν hμ hν hlim a b ha r s hr hs hrs
    (fun i => ((r i) ^ m)⁻¹) ((s ^ m)⁻¹)
    (fun i => le_of_lt (inv_pos.mpr (pow_pos (hr i) m)))
    (le_of_lt (inv_pos.mpr (pow_pos hs m))) hcoeff
  have hseq : (fun i => ENNReal.ofReal (((r i) ^ m)⁻¹) •
      (μ i).map (fun z => (r i)⁻¹ • (z - a i))) =
      (fun i => dimensionalBlowup m (μ i) (a i) (r i)) := by
    funext i
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (hr i) m)]
    rfl
  rw [hseq, ENNReal.ofReal_inv_of_pos (pow_pos hs m)] at hconv
  exact hconv

end Preiss
