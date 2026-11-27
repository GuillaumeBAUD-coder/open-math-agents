import Mathlib

/-!
# A005809: a(n) = binomial(3n,n)

Source: https://oeis.org/A005809
Credit: @niclorusso

Conjecture (Gary Detlefs, Mar 23 2013, in the comments of A005809): a(n) == 3 (mod n^3) iff n is
an odd prime. The comment adds that the direction for odd primes p, binomial(3p, p) == 3 (mod p^3),
is a known generalization of Wolstenholme's theorem; the open part is the converse.

Conventions:
* a(n) = binomial(3n, n) = `Nat.choose (3 * n) n`, offset 0.
* The congruence is `Nat.ModEq (n ^ 3) (a n) 3`.
* n ranges over n >= 2. For n = 1 every integer is congruent to 3 modulo 1^3 = 1, so the
  equivalence would fail for the trivial reason that 1 is not prime; the conjecture is about the
  moduli n^3 with n > 1 (and for n = 0, a(0) = 1 is not congruent to 3 modulo 0 anyway).
-/

namespace OMA.S_oeis_a005809

/-- Detlefs' conjecture on A005809: for `n >= 2`, `binomial(3n, n) == 3 (mod n^3)` if and only if
`n` is an odd prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((Nat.choose (3 * n) n ≡ 3 [MOD n ^ 3]) ↔ (n.Prime ∧ Odd n)) := by
  sorry

end OMA.S_oeis_a005809
