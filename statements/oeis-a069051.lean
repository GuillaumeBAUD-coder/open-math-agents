import Mathlib

/-!
# A069051: Primes p such that p-1 divides 2^p-2.

Source: https://oeis.org/A069051
Credit: @divmxnd0x

Conjecture (Thomas Ordowski, Nov 20 2018, stated in A069051): if `n - 1` divides `2^n - 2`, then
`(2^n - 2)/(n - 1)` is squarefree.

Formalization notes:
* Stated for `n ≥ 2` (for `n = 1` the "quotient" `0/0` is meaningless); the terms with
  `n - 1 ∣ 2^n - 2` are `2, 3, 7, 19, 43, 55, 127, ...`, and the quotient is exact.
-/

namespace OMA.S_oeis_a069051

/-- Ordowski's conjecture: for `n ≥ 2` with `n - 1 ∣ 2^n - 2`, `(2^n - 2)/(n - 1)` is squarefree. -/
theorem main : ∀ n : ℕ, 2 ≤ n → n - 1 ∣ 2 ^ n - 2 → Squarefree ((2 ^ n - 2) / (n - 1)) := by
  sorry

end OMA.S_oeis_a069051
