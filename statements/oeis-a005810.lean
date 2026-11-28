import Mathlib

/-!
# A005810: binomial(4n, n) modulo n^3

Source: https://oeis.org/A005810
Credit: @jagraj28

A005810 is `a(n) = binomial(4n, n)`. The entry records a conjecture of Gary Detlefs (2013):
`a(n) ≡ 4 (mod n^3)` if and only if `n` is prime.

`main` states it for `n ≥ 2`. For `n = 1` every integer is `≡ 4 (mod 1)` while 1 is not prime,
so the literal statement fails there for a trivial reason; the source plainly means `n ≥ 2`.
(For `n = 0` the congruence `1 ≡ 4 (mod 0)` is false, consistent with 0 not being prime.)
A check for `2 ≤ n ≤ 1500` finds no exception.
-/

namespace OMA.S_oeis_a005810

/-- Detlefs's conjecture in OEIS A005810. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ((4 * n).choose n ≡ 4 [MOD n ^ 3] ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a005810
