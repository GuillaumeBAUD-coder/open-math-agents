import Mathlib

/-!
# A256438: Numbers m such that sigma(sigma(m-1)) = 2*(m-1).

Source: https://oeis.org/A256438
Credit: @azmiozgen

Conjecture (from the entry): the terms are the numbers of the form 2^k+1 such that sigma(2^k)
is a prime p.

Formalization notes:
* The terms are m ≥ 2 (offset 1, first term 3); m = 1 is excluded because Mathlib sets
  sigma(0) = 0, which would make m = 1 satisfy the equation formally.
* The conjecture is stated as a characterization of all m ≥ 2:
  sigma(sigma(m-1)) = 2(m-1) if and only if m = 2^k + 1 for some k with sigma(2^k) prime.
  (k = 0 gives sigma(1) = 1, which is not prime.)
* Controls (computed): the terms up to 70000 are 3, 5, 17, 65, 4097, 65537, as in the entry.
-/

namespace OMA.S_oeis_a256438

open ArithmeticFunction

/-- The terms of A256438 are the numbers `2^k + 1` with `σ(2^k)` prime. -/
theorem main :
    ∀ m : ℕ, 2 ≤ m →
      (sigma 1 (sigma 1 (m - 1)) = 2 * (m - 1) ↔
        ∃ k : ℕ, m = 2 ^ k + 1 ∧ (sigma 1 (2 ^ k)).Prime) := by
  sorry

end OMA.S_oeis_a256438
