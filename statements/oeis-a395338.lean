import Mathlib

/-!
# A395338: Primes whose square is a concatenation of two distinct nonzero squares

Source: https://oeis.org/A395338

Conjecture (OEIS A395338):
There are infinitely many primes `p` whose square `p^2` has a base-10 representation
that is the concatenation of the base-10 representations of two distinct nonzero
squares `a^2` and `b^2` (with no leading zeros).

Conventions:
- Offset: `1`; first terms: `7, 13, 19, 41, 223, 487, 1201, 1301, 18493, 32009, ...`.
- For `p = 7`, `7^2 = 49 = 4 || 9` (`2^2` and `3^2`); for `p = 13`,
  `13^2 = 169 = 16 || 9` (`4^2` and `3^2`).
- For `a, b ≥ 1`, `(Nat.digits 10 (a ^ 2)).reverse` and `(Nat.digits 10 (b ^ 2)).reverse`
  are the standard most-significant-digit-first decimal representations with no leading
  zeros.
-/

namespace OMA.S_oeis_a395338

/-- Predicate stating that the base-10 expansion of `p^2` is the concatenation of two
distinct nonzero squares `a^2` and `b^2` (OEIS A395338). -/
def IsConcatTwoDistinctSquares (p : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a ≠ b ∧
    (Nat.digits 10 (p ^ 2)).reverse =
      (Nat.digits 10 (a ^ 2)).reverse ++ (Nat.digits 10 (b ^ 2)).reverse

/-- The set of primes `p` in OEIS A395338. -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ IsConcatTwoDistinctSquares p}

/-- Conjecture: the sequence A395338 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a395338
