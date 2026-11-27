import Mathlib

/-!
# MathOverflow 66891

Source: https://mathoverflow.net/questions/66891
-/

namespace OMA.S_mo_66891

open MeasureTheory Filter
open scoped ENNReal

theorem main : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (A : ℕ → Set α),
      (∀ n, MeasurableSet (A n)) → (∑' n, μ (A n)) ≠ ∞ →
        μ (Filter.limsup A Filter.atTop) = 0 := by
  sorry

end OMA.S_mo_66891
