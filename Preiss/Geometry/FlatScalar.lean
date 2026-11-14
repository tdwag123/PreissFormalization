module

public import Preiss.Geometry.FlatMeasure

/-! # Positive finite scalar multiplication of flat measures -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem IsFlat.smul {ν : Measure (Euclidean n)} (hν : IsFlat m ν)
    {c : ℝ≥0∞} (hc : 0 < c) (hctop : c < ∞) : IsFlat m (c • ν) := by
  obtain ⟨V, d, hd, hdtop, rfl⟩ := hν
  exact ⟨V, c * d, ENNReal.mul_pos_iff.mpr ⟨hc, hd⟩, ENNReal.mul_lt_top hctop hdtop, smul_smul c d _⟩

theorem isFlat_smul_iff (ν : Measure (Euclidean n)) {c : ℝ≥0∞}
    (hc : 0 < c) (hctop : c < ∞) : IsFlat m (c • ν) ↔ IsFlat m ν := by
  constructor
  · intro h
    have hh := h.smul (ENNReal.inv_pos.mpr hctop.ne)
      (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hc.ne'))
    simpa only [smul_smul, ENNReal.inv_mul_cancel hc.ne' hctop.ne, one_smul] using hh
  · exact fun h => h.smul hc hctop

end Preiss
