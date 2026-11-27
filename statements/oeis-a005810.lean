import Mathlib

/-!
# A005810: a(n) = binomial(4n,n)

Source: https://oeis.org/A005810
Credit: @niclorusso

Conjecture (Gary Detlefs, in the comments of A005810): a(n) == 4 (mod n^3) iff n is prime.

Conventions:
* a(n) = binomial(4n, n) = `Nat.choose (4 * n) n`, offset 0.
* The congruence is `Nat.ModEq (n ^ 3) (a n) 4`.
* n ranges over n >= 2. For n = 1 every integer is congruent to 4 modulo 1^3 = 1, so the
  equivalence would fail for the trivial reason that 1 is not prime; the conjecture is about the
  moduli n^3 with n > 1 (and for n = 0, a(0) = 1 is not congruent to 4 modulo 0 anyway).
-/

namespace OMA.S_oeis_a005810

/-- Detlefs' conjecture on A005810: for `n >= 2`, `binomial(4n, n) == 4 (mod n^3)` if and only if
`n` is prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ((Nat.choose (4 * n) n ≡ 4 [MOD n ^ 3]) ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a005810
