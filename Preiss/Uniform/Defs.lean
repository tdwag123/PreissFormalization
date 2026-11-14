module

public import Preiss.Tangent.Blowup
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Regular

/-! # Unit uniform and conical measures

The ball law is independent of any tangent-measure construction.
The bridge to FormalizingGMT's `IsSUniform` is a separate adapter.
-/

@[expose] public section
open MeasureTheory Metric
namespace Preiss
variable {n : Nat}

/-- A regular measure with the origin in its support and unit uniform ball law.
Dimension zero is allowed; results requiring positive dimension say so explicitly. -/
def IsUnitUniform (m : ℕ) (ν : Measure (Euclidean n)) : Prop :=
  ν.Regular ∧ (0 : Euclidean n) ∈ ν.support ∧
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ν (closedBall x r) = ENNReal.ofReal (r ^ m)

def IsConical (m : ℕ) (ν : Measure (Euclidean n)) : Prop :=
  ∀ r : ℝ, 0 < r → dimensionalBlowup m ν 0 r = ν

end Preiss
