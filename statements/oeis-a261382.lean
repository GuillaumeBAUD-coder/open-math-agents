import Mathlib

/-!
# A261382: Least positive integer k such that (k-1)^2+(k*n)^2, k^2+(k*n-1)^2, (k+1)^2+(k*n)^2 and k^2+(k*n+1)^2 are all prime.

Source: https://oeis.org/A261382
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261382): `a(n)` exists for any `n > 0`. In general, any positive
rational number `r` can be written as `m/n`, where `m` and `n` are positive integers with
`(m-1)^2 + n^2`, `m^2 + (n-1)^2`, `(m+1)^2 + n^2` and `m^2 + (n+1)^2` all prime. (The existence of
`a(n)` is the case `r = n`, with numerator `k n` and denominator `k`.)

Formalization notes:
* For positive `m, n` the subtractions `m - 1`, `n - 1` in `ℕ` are exact.
* With this definition `a(1), a(3), a(4), a(5)` = 2, 15, 30, 5, matching the data of A261382.
-/

namespace OMA.S_oeis_a261382

/-- Sun's conjecture of A261382. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ r = (m : ℚ) / n ∧
    ((m - 1) ^ 2 + n ^ 2).Prime ∧ (m ^ 2 + (n - 1) ^ 2).Prime ∧ ((m + 1) ^ 2 + n ^ 2).Prime ∧
    (m ^ 2 + (n + 1) ^ 2).Prime := by
  sorry

end OMA.S_oeis_a261382
