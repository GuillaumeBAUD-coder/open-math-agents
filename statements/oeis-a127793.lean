import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace OMA.S_oeis_a127793

/-- Lower triangular rational matrix `t(n, k) = 1 / ⌊(n+2)/2⌋` if `1 ≤ k ≤ n ≤ 2k`, else `0`. -/
def tMat (n k : ℕ) : ℚ :=
  if 1 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k then 1 / (((n + 2) / 2 : ℕ) : ℚ) else 0

/-- OEIS A127793 conjectures:
1. Row sums of `tMat` equal `1` for every `n ≥ 1`.
2. There exists a lower triangular integer triangle `T : ℕ → ℕ → ℤ` (with `T n k = 0` for `k > n`)
   which is the exact matrix inverse of `tMat` (`∑_{j=1}^n tMat n j * T j k = δ_{n,k}` and
   `∑_{j=1}^n T n j * tMat j k = δ_{n,k}` for `1 ≤ k ≤ n`).
3. Row sums of `T` equal `1` for every `n ≥ 1`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, tMat n k = 1) ∧
    ∃ T : ℕ → ℕ → ℤ,
      (∀ n k : ℕ, n < k → T n k = 0) ∧
      (∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
        ∑ j ∈ Finset.Icc 1 n, tMat n j * (T j k : ℚ) = if n = k then 1 else 0) ∧
      (∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
        ∑ j ∈ Finset.Icc 1 n, (T n j : ℚ) * tMat j k = if n = k then 1 else 0) ∧
      (∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = 1) := by
  sorry

end OMA.S_oeis_a127793
