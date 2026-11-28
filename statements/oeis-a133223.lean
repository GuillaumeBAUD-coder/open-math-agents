import Mathlib

/-!
# A133223: Sum of digits of primes (A007605), sorted and with duplicates removed.

Source: https://oeis.org/A133223
Credit: @divmxnd0x

Conjecture (Chai Wah Wu, Nov 04 2018, stated in A133223): for `s > 10` and not a multiple of 3,
there exists a prime with digit-sum `s` consisting only of the digits 2 and 3 (verified for
`s ≤ 2995`).

Formalization notes:
* Digits and digit sums are in base 10. Only this first conjecture of the comment (digits 2 and 3)
  is formalized.
-/

namespace OMA.S_oeis_a133223

/-- For every `s > 10` with `¬ 3 ∣ s` there is a prime whose decimal digits are all 2 or 3 and sum
to `s`. -/
theorem main : ∀ s : ℕ, 10 < s → ¬ 3 ∣ s →
    ∃ p : ℕ, p.Prime ∧ (∀ d ∈ Nat.digits 10 p, d = 2 ∨ d = 3) ∧ (Nat.digits 10 p).sum = s := by
  sorry

end OMA.S_oeis_a133223
