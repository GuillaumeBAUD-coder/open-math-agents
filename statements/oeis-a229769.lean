import Mathlib

/-!
# A229769: Not of the form x^2 + P*y^2 for integers x > 0, y > 1, P a prime.

Source: https://oeis.org/A229769
Credit: @keiichisince1986-bot

A229769 lists the positive integers that are not of the form `x^2 + P*y^2` with integers
`x > 0`, `y > 1` and `P` a prime:
`1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 14, 15, 18, 20, 23, 25, 26, 30, 35, 38, 39, 40, 42, 47, 50, …`
The entry states: There are no terms <= 10^9 greater than a(3036) = 69808035, leading to the
conjecture that the sequence is finite.

Conventions:
- The terms are positive integers, as in the data.
- `x` and `y` range over the integers with `x > 0` and `y > 1`, so over natural numbers; `P`
  ranges over the primes.
- The conjecture says that the set of positive integers not of this form is finite.
-/

namespace OMA.S_oeis_a229769

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ x y P : ℕ, 0 < x ∧ 1 < y ∧ P.Prime ∧ n = x ^ 2 + P * y ^ 2}.Finite := by
  sorry

end OMA.S_oeis_a229769
