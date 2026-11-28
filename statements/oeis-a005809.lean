import Mathlib

/-!
# A005809: a(n) = binomial(3n,n).

Source: https://oeis.org/A005809
Credit: @AgentsAlex

Conjecture (Gary Detlefs, Mar 23 2013): a(n) ≡ 3 (mod n^3) iff n is an odd prime.

The direction "n an odd prime ⟹ a(n) ≡ 3 (mod n^3)" is a known generalization of Wolstenholme's
theorem (Peter Bala's comment on the entry, citing Mestrovic, Section 6, equation 35); the open
part is the converse.

Formalization notes:
* `a n` is `Nat.choose (3 * n) n` (offset 0, as in the entry).
* The index ranges over `n ≥ 2`. For `n = 1` every integer is congruent to 3 modulo `1 ^ 3 = 1`,
  so `a(1) = 3 ≡ 3 (mod 1)` holds while 1 is not an odd prime: read literally the biconditional
  fails at this degenerate modulus, so the standard reading excludes it. (`n = 0` would be
  harmless: modulo `0` the congruence is equality and `a(0) = 1 ≠ 3`; the range simply starts
  after the degenerate case.)
* With these definitions the congruence holds for exactly the odd primes among `2 ≤ n ≤ 3000`.
-/

namespace OMA.S_oeis_a005809

/-- A005809: `a(n) = binomial(3n, n)`. -/
def a (n : ℕ) : ℕ :=
  Nat.choose (3 * n) n

/-- Detlefs' conjecture: for `n ≥ 2`, `a(n) ≡ 3 (mod n^3)` if and only if `n` is an odd prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → (a n ≡ 3 [MOD n ^ 3] ↔ n.Prime ∧ Odd n) := by
  sorry

end OMA.S_oeis_a005809
