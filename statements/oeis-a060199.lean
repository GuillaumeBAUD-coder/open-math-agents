import Mathlib

/-!
# A060199: Number of primes between n^3 and (n+1)^3.

Source: https://oeis.org/A060199
Credit: @divmxnd0x

a(n) is the number of primes `p` with `n^3 < p < (n+1)^3` (offset 0).

Conjecture (Cino Hilliard, Jan 05 2003): there are always more than 3 primes between two
consecutive nonzero cubes, i.e. `a(n) > 3` for every `n ≥ 1`.

Known: Dudek (2014), improved by Cully-Hugill (2021) and by Mossinghoff, Trudgian and Yang (2024),
proves `a(n) > 0` for every `n > exp(exp(32.76))`; the statement for all `n ≥ 1` is open.

Formalization notes:
* Cubes `k^3` with `k ≥ 1` are never prime (`1` is not prime, and `k^3` has the divisor `k`
  otherwise), so counting primes in the open interval `(n^3, (n+1)^3)` agrees with counting them
  in the closed interval, as the OEIS programs do.
* "Two consecutive nonzero cubes" are `n^3` and `(n+1)^3` with `n ≥ 1`; for `n = 0` there is no
  prime in `(0, 1)`, which is why the source excludes the zero cube.
* With this definition `a 0, ..., a 15` are 0, 4, 5, 9, 12, 17, 21, 29, 32, 39, 49, 52, 58, 73,
  76, 88, matching the data of A060199.
-/

namespace OMA.S_oeis_a060199

/-- A060199(n): the number of primes strictly between `n^3` and `(n+1)^3`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo (n ^ 3) ((n + 1) ^ 3)).filter Nat.Prime).card

/-- Hilliard's conjecture: more than 3 primes lie between any two consecutive nonzero cubes. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 3 < a n := by
  sorry

end OMA.S_oeis_a060199
