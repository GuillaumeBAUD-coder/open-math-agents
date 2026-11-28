import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace OMA.S_oeis_a123120

/-- `IsSumPosSquares n m` means `m` can be written as a sum of `n` squares of positive integers. -/
def IsSumPosSquares (n m : ℕ) : Prop :=
  ∃ f : Fin n → ℕ, (∀ i, 0 < f i) ∧ ∑ i : Fin n, (f i) ^ 2 = m

/-- OEIS A123120 (Dubouis 1911 / Grosswald Theorem 2): for every `n ≥ 6`, a positive integer `m`
is a sum of `n` nonzero squares if and only if `m ≥ n` and
`m ∉ {n + 1, n + 2, n + 4, n + 5, n + 7, n + 10, n + 13}` (leaving exactly `n + 6` positive
integers that cannot be written as sums of `n` nonzero squares). -/
theorem main :
    ∀ n : ℕ, 6 ≤ n → ∀ m : ℕ, 1 ≤ m →
      (IsSumPosSquares n m ↔
        n ≤ m ∧ m ≠ n + 1 ∧ m ≠ n + 2 ∧ m ≠ n + 4 ∧ m ≠ n + 5 ∧
        m ≠ n + 7 ∧ m ≠ n + 10 ∧ m ≠ n + 13) := by
  sorry

end OMA.S_oeis_a123120
