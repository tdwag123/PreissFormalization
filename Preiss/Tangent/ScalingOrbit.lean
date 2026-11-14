import Preiss.Analysis.Vague.Support
import Preiss.Analysis.ProperMeasureTransport
import Preiss.Analysis.Vague.Map
import Preiss.Tangent.Defs
import Preiss.Uniform.Defs
import Preiss.Uniform.Compactness

open MeasureTheory Filter Set Topology
namespace Preiss
variable {n m : ℕ}

/-- Sequential closure of support-centered dimensional rescalings with radius at most one.
No small-radius limit is required, so this differs from a tangent measure at one point. -/
def IsUniformPseudotangent (m : ℕ) (ν ξ : Measure (Euclidean n)) : Prop :=
  ξ.Regular ∧ ∃ (a : ℕ → Euclidean n) (r : ℕ → ℝ),
    (∀ i, a i ∈ ν.support) ∧ (∀ i, 0 < r i ∧ r i ≤ 1) ∧
      Measure.WeaklyConverges (fun i => dimensionalBlowup m ν (a i) (r i)) ξ

/-- A dimensional tangent at a support point belongs to the bounded-radius scaling orbit. -/
theorem IsDimensionalTangent.isUniformPseudotangent
    {ν ξ : Measure (Euclidean n)} {y : Euclidean n}
    (h : IsDimensionalTangent m ν ξ y) (hy : y ∈ ν.support) :
    IsUniformPseudotangent m ν ξ := by
  obtain ⟨hreg, hne, r, hr, hr0, hlim⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hr0.eventually (eventually_lt_nhds zero_lt_one))
  have hshift : Tendsto (fun i : ℕ => i + N) atTop atTop := tendsto_add_atTop_nat N
  refine ⟨hreg, fun _ => y, fun i => r (i + N), fun _ => hy,
    fun i => ⟨hr _, (hN _ (Nat.le_add_left N i)).le⟩, ?_⟩
  exact fun f => (hlim f).comp hshift

theorem uniformPseudotangent_isUnitUniform (ν ξ : Measure (Euclidean n))
    (hν : IsUnitUniform m ν) (hξ : IsUniformPseudotangent m ν ξ) :
    IsUnitUniform m ξ := by
  obtain ⟨hreg, a, r, ha, hr, hlim⟩ := hξ
  exact isUnitUniform_of_vague (fun i => dimensionalBlowup m ν (a i) (r i))
    (fun i => isUnitUniform_dimensionalBlowup ν hν (a i) (ha i) (hr i).1) ξ hreg hlim

/-- The scaling-orbit transitivity argument uses only source regularity. -/
theorem uniformPseudotangent_trans_of_regular (ν ξ ζ : Measure (Euclidean n))
    (hν : ν.Regular) (hξ : IsUniformPseudotangent m ν ξ)
    (hζ : IsUniformPseudotangent m ξ ζ) : IsUniformPseudotangent m ν ζ := by
  classical
  obtain ⟨hξreg, a, r, ha, hr, hfirst⟩ := hξ
  obtain ⟨hζreg, b, s, hb, hs, hsecond⟩ := hζ
  let ν' (j : ℕ) := dimensionalBlowup m ν (a j) (r j)
  have hν'reg (j : ℕ) : (ν' j).Regular := regular_dimensionalBlowup ν hν (a j) (hr j).1
  have hcenters (i : ℕ) : ∃ c : ℕ → Euclidean n,
      (∀ᶠ j in atTop, c j ∈ (ν' j).support) ∧ Tendsto c atTop (𝓝 (b i)) :=
    exists_support_sequence_of_vague ν' ξ hν'reg hξreg hfirst (b i) (hb i)
  choose c hcSupport hcConv using hcenters
  let rows (i j : ℕ) := dimensionalBlowup m ν (a j + r j • c i j) (r j * s i)
  let limits (i : ℕ) := dimensionalBlowup m ξ (b i) (s i)
  have hcomp (i j : ℕ) : dimensionalBlowup m (ν' j) (c i j) (s i) = rows i j :=
    dimensionalBlowup_comp ν (a j) (c i j) (r j) (s i) (hr j).1 (hs i).1
  have hrows (i : ℕ) : Measure.WeaklyConverges (rows i) (limits i) := by
    have h := vague_dimensionalBlowup_moving (m := m) ν' ξ hν'reg hξreg hfirst
      (c i) (b i) (hcConv i) (fun _ => s i) (s i) (fun _ => (hs i).1)
      (hs i).1 tendsto_const_nhds
    simpa only [hcomp] using h
  have hrowsreg (i j : ℕ) : (rows i j).Regular :=
    regular_dimensionalBlowup ν hν _ (mul_pos (hr j).1 (hs i).1)
  have hlimitsreg (i : ℕ) : (limits i).Regular :=
    regular_dimensionalBlowup ξ hξreg (b i) (hs i).1
  obtain ⟨j, hj, hdiag⟩ := vague_diagonal_selection rows limits ζ hrowsreg hlimitsreg
    hζreg hrows hsecond (fun i j => c i j ∈ (ν' j).support) hcSupport
  refine ⟨hζreg, (fun i => a (j i) + r (j i) • c i (j i)),
    (fun i => r (j i) * s i), ?_, ?_, hdiag⟩
  · intro i
    have hi := (hj i).2
    change c i (j i) ∈ (dimensionalBlowup m ν (a (j i)) (r (j i))).support at hi
    rw [dimensionalBlowup_support ν (a (j i)) (hr (j i)).1] at hi
    obtain ⟨y, hy, heq⟩ := hi
    have hcenter : a (j i) + r (j i) • c i (j i) = y := by
      rw [← heq, smul_smul, mul_inv_cancel₀ (hr (j i)).1.ne', one_smul]
      abel
    change a (j i) + r (j i) • c i (j i) ∈ ν.support
    rw [hcenter]
    exact hy
  · intro i
    refine ⟨mul_pos (hr (j i)).1 (hs i).1, ?_⟩
    calc r (j i) * s i ≤ 1 * s i :=
        mul_le_mul_of_nonneg_right (hr (j i)).2 (hs i).1.le
      _ ≤ 1 := by simpa only [one_mul] using (hs i).2

theorem uniformPseudotangent_trans (ν ξ ζ : Measure (Euclidean n))
    (hν : IsUnitUniform m ν) (hξ : IsUniformPseudotangent m ν ξ)
    (hζ : IsUniformPseudotangent m ξ ζ) : IsUniformPseudotangent m ν ζ :=
  uniformPseudotangent_trans_of_regular ν ξ ζ hν.1 hξ hζ

theorem uniformPseudotangent_map_linearIsometry {k : ℕ}
    (L : Euclidean n →ₗᵢ[ℝ] Euclidean k) (ν ξ : Measure (Euclidean n))
    (hν : IsUnitUniform m ν) (hξ : IsUniformPseudotangent m ν ξ) :
    IsUniformPseudotangent m (ν.map L) (ξ.map L) := by
  obtain ⟨hξreg, a, r, ha, hr, hlim⟩ := hξ
  have hL := L.isometry.isClosedEmbedding
  refine ⟨regular_map_of_isProperMap L hL.isProperMap ξ hξreg,
    fun i => L (a i), r, ?_, hr, ?_⟩
  · intro i
    rw [measure_support_map_of_continuous_of_isClosedMap L L.continuous
      hL.isClosedMap ν hν.1]
    exact Set.mem_image_of_mem L (ha i)
  · have hmap := weaklyConverges_map_of_isProperMap L hL.isProperMap _ _ hlim
    have heq (i : ℕ) : dimensionalBlowup m (ν.map L) (L (a i)) (r i) =
        (dimensionalBlowup m ν (a i) (r i)).map L :=
      dimensionalBlowup_map_linearIsometry L ν (a i) (r i) (hr i).1
    simpa only [heq] using hmap


end Preiss
