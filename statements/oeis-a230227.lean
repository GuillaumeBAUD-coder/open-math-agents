import Mathlib

/-!
# A230227: Primes p with 3*p - 10 also prime.

Source: https://oeis.org/A230227
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): for any integer n > 4 not equal to 76, we have 2n = p + q
for some terms p and q from the sequence.

Formalization notes:
* Terms are primes p with 3p - 10 prime (3p - 10 > 0 for p ≥ 5; for p = 2, 3 the ℕ value 0 is not
  prime, matching negative values not being prime).
* Controls (computed): for 4 < n < 8000, n ≠ 76, such p, q exist; for n = 76 they do not.
-/

namespace OMA.S_oeis_a230227

/-- `p` is a term: `p` and `3p - 10` are prime. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ (3 * p - 10).Prime

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 4 < n → n ≠ 76 → ∃ p q : ℕ, IsTerm p ∧ IsTerm q ∧ p + q = 2 * n := by
  sorry

end OMA.S_oeis_a230227
