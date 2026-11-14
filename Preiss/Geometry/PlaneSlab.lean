module

public import Preiss.Geometry.Planes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

/-! # Hausdorff measure bounds for slabs in finite-dimensional planes -/

@[expose] public section
open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace Preiss
variable {m n : ℕ}


set_option maxHeartbeats 1500000 in
theorem hausdorffMeasure_plane_slab_le (m n : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Plane m n) (c v : Euclidean n) (R d : ℝ),
      c ∈ V.1 → v ∈ V.1 → ‖v‖ = 1 → 0 ≤ R → 0 ≤ d →
      (Measure.hausdorffMeasure (m : ℝ))
        {z | z ∈ V.1 ∧ ‖z - c‖ ≤ R ∧ |inner ℝ v (z - c)| ≤ d * R} ≤
      ENNReal.ofReal (C * d * R ^ m) := by
  classical
  let L : ℝ≥0 := (Fintype.card (Fin m) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal
  let C : ℝ := (L : ℝ) ^ m * 2 ^ m + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro V c v R d hc hv hvnorm hR hd
  let i₀ : Fin m := ⟨0, hm⟩
  let vV : V.1 := ⟨v, hv⟩
  have hsingle : Orthonormal ℝ (({i₀} : Set (Fin m)).domRestrict (fun _ ↦ vV)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hvnorm
  obtain ⟨b, hb⟩ := hsingle.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ V.1 = Fintype.card (Fin m) by simp [V.property])
  have hb₀ : b i₀ = vV := hb i₀ (mem_singleton i₀)
  let w : Fin m → ℝ := fun i ↦ if i = i₀ then d * R else R
  let lo : Fin m → ℝ := fun i ↦ -w i
  let hi : Fin m → ℝ := w
  let B : Set (Fin m → ℝ) := Icc lo hi
  let f : (Fin m → ℝ) → Euclidean n := fun u ↦ c +
    ((b.repr.symm (WithLp.toLp 2 u) : V.1) : Euclidean n)
  have hiso : Isometry (fun u : EuclideanSpace ℝ (Fin m) ↦
      c + ((b.repr.symm u : V.1) : Euclidean n)) := by
    apply Isometry.of_dist_eq
    intro x y
    rw [dist_add_left]
    change dist (b.repr.symm x) (b.repr.symm y) = dist x y
    exact b.repr.symm.isometry.dist_eq x y
  have hf : LipschitzWith L f := by
    simpa only [L, f, Function.comp_def, one_mul] using hiso.lipschitzWith.comp
      (PiLp.lipschitzWith_toLp 2 (fun _ : Fin m ↦ ℝ))
  have hsub : {z | z ∈ V.1 ∧ ‖z - c‖ ≤ R ∧ |inner ℝ v (z - c)| ≤ d * R} ⊆ f '' B := by
    intro z hz
    let zV : V.1 := ⟨z - c, V.1.sub_mem hz.1 hc⟩
    let u : Fin m → ℝ := WithLp.ofLp (b.repr zV)
    have hcoord (i : Fin m) : |u i| ≤ w i := by
      change |b.repr zV i| ≤ _
      rw [b.repr_apply_apply]
      by_cases hi : i = i₀
      · subst i
        rw [hb₀]
        exact hz.2.2
      · dsimp [w]
        rw [if_neg hi]
        have hh := abs_real_inner_le_norm (b i) zV
        rw [b.orthonormal.norm_eq_one i, one_mul] at hh
        exact hh.trans hz.2.1
    refine ⟨u, ?_, ?_⟩
    · constructor
      · intro i
        exact (abs_le.mp (hcoord i)).1
      · intro i
        exact (abs_le.mp (hcoord i)).2
    · dsimp [f, u]
      rw [b.repr.symm_apply_apply]
      change c + (z - c) = z
      abel
  have hbox : (volume : Measure (Fin m → ℝ)) B =
      ENNReal.ofReal (2 * d * R) * ENNReal.ofReal (2 * R) ^ (m - 1) := by
    rw [Real.volume_Icc_pi]
    have hterm (i : Fin m) : ENNReal.ofReal (hi i - lo i) =
        if i = i₀ then ENNReal.ofReal (2 * d * R) else ENNReal.ofReal (2 * R) := by
      dsimp only [hi, lo, w]
      split_ifs <;> congr 1 <;> ring
    simp_rw [hterm]
    rw [← Finset.mul_prod_erase Finset.univ (fun i : Fin m ↦
      if i = i₀ then ENNReal.ofReal (2 * d * R) else ENNReal.ofReal (2 * R))
      (Finset.mem_univ i₀)]
    rw [if_pos rfl]
    congr 1
    calc
      (∏ i ∈ Finset.univ.erase i₀,
        if i = i₀ then ENNReal.ofReal (2 * d * R) else ENNReal.ofReal (2 * R)) =
          ∏ _i ∈ Finset.univ.erase i₀, ENNReal.ofReal (2 * R) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi)]
      _ = _ := by simp
  have hHPi : (Measure.hausdorffMeasure (m : ℝ) : Measure (Fin m → ℝ)) = volume := by
    simpa only [Fintype.card_fin] using (hausdorffMeasure_pi_real (ι := Fin m))
  have hmass := (measure_mono hsub).trans (hf.hausdorffMeasure_image_le (d := (m : ℝ)) (by positivity) B)
  rw [hHPi, hbox, ENNReal.rpow_natCast] at hmass
  have hfactor : (L : ℝ≥0∞) ^ m *
      (ENNReal.ofReal (2 * d * R) * ENNReal.ofReal (2 * R) ^ (m - 1)) =
      ENNReal.ofReal ((L : ℝ) ^ m * 2 ^ m * d * R ^ m) := by
    have hRpow : R ^ m = R ^ (m - 1) * R := by rw [← pow_succ, Nat.sub_add_cancel hm]
    have h2pow : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hm]
    have halg : (L : ℝ) ^ m * 2 ^ m * d * R ^ m =
        ((L : ℝ) ^ m * (2 * d * R)) * (2 * R) ^ (m - 1) := by
      rw [mul_pow, hRpow, h2pow]
      ring
    rw [halg]
    symm
    rw [ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) ^ m * (2 * d * R) by positivity),
      ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) ^ m by positivity),
      ENNReal.ofReal_pow (show 0 ≤ (L : ℝ) from L.property) m,
      ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_pow (show 0 ≤ 2 * R by positivity) (m - 1)]
    ring
  rw [hfactor] at hmass
  apply hmass.trans
  apply ENNReal.ofReal_le_ofReal
  dsimp [C]
  nlinarith [mul_nonneg hd (pow_nonneg hR m)]

end Preiss
