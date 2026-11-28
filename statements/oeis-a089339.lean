import Mathlib

/-!
# A089339: Number of primes beginning with n and of the form n concatenated with p where p takes all the prime values less than n.

Source: https://oeis.org/A089339
Credit: @darealpandaboi

Conjecture: there are finitely many zeros in this sequence.

Translation notes.
* The concatenation of n and p in decimal is n * 10^(number of digits of p) + p.
  a(n) counts primes p < n with this concatenation prime; a(n) = 0 when there is none.
* This reproduces all listed terms (checked by computer). Below 5000 the zeros are at
  n = 1, 2, 3, 6, 14. The question whether 14 is the largest is not part of the statement.
-/

namespace OMA.S_oeis_a089339

theorem main :
    {n : ℕ | 1 ≤ n ∧
      ¬ ∃ p : ℕ, p.Prime ∧ p < n ∧ (n * 10 ^ (Nat.digits 10 p).length + p).Prime}.Finite := by
  sorry

end OMA.S_oeis_a089339
