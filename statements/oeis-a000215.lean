import Mathlib

/-!
# A000215: Fermat numbers: a(n) = 2^(2^n) + 1.

Source: https://oeis.org/A000215
Credit: @rabdelaal

OEIS A000215 records the conjecture that just the first 5 Fermat numbers are prime, i.e.
`2 ^ 2 ^ n + 1` is composite for every `n ≥ 5` (the primes are `F0 = 3` through
`F4 = 65537`).
-/

namespace OMA.S_oeis_a000215

/-- The Fermat number `F n = 2 ^ 2 ^ n + 1` (OEIS A000215). -/
def fermatNumber (n : ℕ) : ℕ :=
  2 ^ 2 ^ n + 1

/-- The conjecture recorded in OEIS A000215: only the first five Fermat numbers are
prime, that is, `F n` is not prime for `n ≥ 5`. -/
theorem main : ∀ n ≥ 5, ¬ Nat.Prime (fermatNumber n) := by
  sorry

end OMA.S_oeis_a000215
