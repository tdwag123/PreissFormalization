import Preiss.Rectifiability.MarstrandMattila.SetCriterion
import Preiss.Density.FinitePieces
import Preiss.Tangent.FlatApproximation
import Preiss.Tangent.Restriction
import Preiss.Density.AbsoluteContinuous

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace Preiss
variable {m n : ℕ}

theorem ae_density_bounds_and_flat_tangents_restrict_hausdorff
    (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (S : Set (Euclidean n)) (hS : MeasurableSet S) (hfin : (Measure.hausdorffMeasure (m : ℝ)) S < ∞)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ENNReal.ofReal a • ((Measure.hausdorffMeasure (m : ℝ))).restrict S ≤ μ.restrict S)
    (hhi : μ.restrict S ≤ ENNReal.ofReal b • ((Measure.hausdorffMeasure (m : ℝ))).restrict S)
    (hd : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x)
    (ht : ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) :
    ∀ᵐ x ∂(((Measure.hausdorffMeasure (m : ℝ))).restrict S), HasPositiveFiniteDensitiesAt m (((Measure.hausdorffMeasure (m : ℝ))).restrict S) x ∧
      ∀ ν, IsTangentMeasure (((Measure.hausdorffMeasure (m : ℝ))).restrict S) ν x → IsFlat m ν := by
  let H : Measure (Euclidean n) := (Measure.hausdorffMeasure (m : ℝ)).restrict S
  haveI : IsFiniteMeasure H := isFiniteMeasure_restrict.mpr hfin.ne
  have hHμ : H ≪ μ :=
    (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.mpr ha).ne').trans
      (Measure.absolutelyContinuous_of_le (hlo.trans Measure.restrict_le_self))
  filter_upwards [ae_hasPositiveFiniteDensitiesAt_of_absolutelyContinuous μ H hHμ hd,
    ae_isTangentMeasure_iff_of_absolutelyContinuous μ H hHμ, hHμ.ae_le ht] with x hx hmatch hflat
  exact ⟨hx, fun ν hν ↦ hflat ν ((hmatch ν).mpr hν)⟩

theorem isRectifiableMeasure_of_ae_density_bounds_and_flat_tangents
    (hm : 0 < m) (hmn : m ≤ n) (μ : Measure (Euclidean n)) [IsLocallyFiniteMeasure μ]
    (hd : ∀ᵐ x ∂μ, HasPositiveFiniteDensitiesAt m μ x)
    (ht : ∀ᵐ x ∂μ, ∀ ν, IsTangentMeasure μ ν x → IsFlat m ν) :
    IsRectifiableMeasure m μ := by
  obtain ⟨S, hS, _, hfin, hcover, hcompare⟩ := exists_finite_hausdorff_pieces_of_density_bounds μ hd
  apply isRectifiableMeasure_of_countable_restrict μ S hS hcover
  intro j
  obtain ⟨a, b, ha, hb, hlo, hhi⟩ := hcompare j
  let H := (Measure.hausdorffMeasure (m : ℝ) : Measure (Euclidean n)).restrict (S j)
  haveI : IsFiniteMeasure H := isFiniteMeasure_restrict.mpr (hfin j).ne
  have htransfer := ae_density_bounds_and_flat_tangents_restrict_hausdorff μ (S j) (hS j)
    (hfin j) ha hb hlo hhi hd ht
  have hw : ∀ᵐ x ∂H, WeaklyLinearlyApproximableAt m (S j) x := by
    filter_upwards [htransfer] with x hx
    exact weaklyLinearlyApproximableAt_of_all_tangents_flat H x hx.1 hx.2
  have hrect := countablyRectifiable_of_ae_weaklyLinearlyApproximableAt hm hmn (S j)
    (hS j) (hfin j) hw
  refine ⟨(Measure.absolutelyContinuous_of_le_smul hhi).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self), S j, hrect, ?_⟩
  rw [Measure.restrict_apply (hS j).compl, compl_inter_self, measure_empty]

end Preiss
