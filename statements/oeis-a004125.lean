import Mathlib

/-!
# OEIS A004125: Pol's conjecture on sums of remainders

Source: https://oeis.org/A004125
Credit: Sudharsan Rajendiran

`a(n) = ∑_{k=1}^{n} (n mod k)` is the sum of the remainders of `n` mod `1, 2, …, n`. Omar E. Pol
observed that if `n` is an even perfect number then `a(n) = a(n - 1) - 1`. Sela Fried (OEIS,
2025): "Pol's conjecture is true (and the converse holds as well)", because
`a(n) - a(n - 1) = 2n - 1 - σ(n)` and `n` is perfect iff `σ(n) = 2n`. We state this proved
result: for `n ≥ 1`, `n` is perfect iff `a(n) = a(n - 1) - 1`. (It contains Pol's conjecture,
since even perfect numbers are perfect.)

Conventions: `a` is computed in `ℕ` and compared in `ℤ`; `Nat.Perfect n` means that the proper
divisors of `n` sum to `n` and `n > 0`, i.e. `σ(n) = 2n`.
-/

namespace OMA.S_oeis_a004125

/-- `a(n) = ∑_{k=1}^{n} (n mod k)`, the sum of remainders of `n` (OEIS A004125). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, n % k

theorem main : ∀ n : ℕ, 1 ≤ n → (n.Perfect ↔ (a n : ℤ) = a (n - 1) - 1) := by
  sorry

end OMA.S_oeis_a004125
