import Mathlib

/-!
# A014945: Numbers k such that k divides 4^k - 1.

Source: https://oeis.org/A014945
Credit: @divmxnd0x

Conjecture (Thomas Ordowski, Dec 24 2018, stated in A014945): if `k` divides `4^k - 1`, then
`(4^k - 1)/k` is squarefree.

Formalization notes:
* The terms are positive integers (`1, 3, 9, 21, 27, ...`); the conjecture is stated for every
  positive `k` with `k ∣ 4^k - 1`, the quotient being exact.
-/

namespace OMA.S_oeis_a014945

/-- Ordowski's conjecture: for every term `k` of A014945, `(4^k - 1)/k` is squarefree. -/
theorem main : ∀ k : ℕ, 0 < k → k ∣ 4 ^ k - 1 → Squarefree ((4 ^ k - 1) / k) := by
  sorry

end OMA.S_oeis_a014945
