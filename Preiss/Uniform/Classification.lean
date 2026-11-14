import Preiss.Uniform.Transport
import Preiss.Uniform.FullDimension
import Preiss.Uniform.FlatMeasure
import Preiss.Geometry.PlaneEmbedding

/-! # Classification of uniform measures supported on a plane

The proof reuses FormalizingGMT's full-dimensional classification after isometric transport.
-/

open MeasureTheory Metric Set
open scoped ENNReal
namespace Preiss
variable {m n : ℕ}

theorem uniformWithConstant_eq_flat_of_support_subset_plane (hm : 0 < m)
    (ν : Measure (Euclidean n)) {q : ℝ} (hν : IsUniformWithConstant m q ν)
    (V : Plane m n) (hsupp : ν.support ⊆ (V.1 : Set (Euclidean n))) :
    ν = ENNReal.ofReal q • unitFlat V := by
  obtain ⟨L, hLV⟩ := exists_linearIsometry_range_plane V
  obtain ⟨μ, hμ, hmap, _, _⟩ := uniformWithConstant_transport L ν hν (by rwa [hLV])
  have href : IsUniformWithConstant m q (ENNReal.ofReal q • unitFlat V) := by
    simpa only [mul_one] using uniformWithConstant_smul (unitFlat V)
      ((isUnitUniform_iff_constant_one _).mp (isUnitUniform_unitFlat V)).1 hν.2.2.1
  have hrefsupp : (ENNReal.ofReal q • unitFlat V).support ⊆ Set.range L := by
    rw [measure_support_smul _ (ENNReal.ofReal_pos.mpr hν.2.2.1).ne', unitFlat_support, hLV]
  obtain ⟨κ, hκ, hκmap, _, _⟩ :=
    uniformWithConstant_transport L (ENNReal.ofReal q • unitFlat V) href hrefsupp
  have heq := uniformWithConstant_eq_of_fullDimension hm μ κ hμ hκ
  calc ν = μ.map L := hmap.symm
    _ = κ.map L := congrArg (fun ρ : Measure (Euclidean m) => ρ.map L) heq
    _ = ENNReal.ofReal q • unitFlat V := hκmap

theorem unitUniform_eq_flat_of_support_subset_plane (hm : 0 < m)
    (ν : Measure (Euclidean n)) (hν : IsUnitUniform m ν)
    (V : Plane m n) (hsupp : ν.support ⊆ (V.1 : Set (Euclidean n))) :
    ν = unitFlat V := by
  simpa using uniformWithConstant_eq_flat_of_support_subset_plane hm ν
    ((isUnitUniform_iff_constant_one ν).mp hν).1 V hsupp

end Preiss
