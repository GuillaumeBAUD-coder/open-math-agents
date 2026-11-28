import Mathlib

/-!
# A078508: Number of primes between sqrt(n^3) and sqrt((n+1)^3).

Source: https://oeis.org/A078508
Credit: @divmxnd0x

Conjecture 1 (stated in A078508): for `n > 1051`, a prime always exists between `n^1.5` and
`(n+1)^1.5`.

Formalization notes:
* `n^1.5` is the real number `sqrt(n^3)`, as in the name of the entry; "between" is strict (the
  endpoints are irrational unless `n` is a perfect square, and a perfect square's `n^1.5` is not
  prime). The last failure below `40000` is `n = 1051`.
-/

namespace OMA.S_oeis_a078508

/-- For `n > 1051` there is a prime strictly between `sqrt(n^3)` and `sqrt((n+1)^3)`. -/
theorem main : ∀ n : ℕ, 1051 < n → ∃ p : ℕ, p.Prime ∧
    Real.sqrt ((n : ℝ) ^ 3) < p ∧ (p : ℝ) < Real.sqrt (((n : ℝ) + 1) ^ 3) := by
  sorry

end OMA.S_oeis_a078508
