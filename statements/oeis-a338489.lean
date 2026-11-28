import Mathlib

/-!
# A338489: Let t be the closest triangular number to n! (in case n=2, the only case where we have a tie, take the larger t); then a(n) = n! - t.

Source: https://oeis.org/A338489
Credit: @darealpandaboi

Conjecture: 0! = 1, 1! = 1, 3! = 6 and 5! = 120 are the only numbers that are both factorial
(A000142) and triangular (A000217) numbers.

Translation notes.
* Triangular numbers are m(m+1)/2 for m >= 0. The statement says the set of numbers that are
  both a factorial and triangular is exactly {1, 6, 120}.
* A computer check of n! for n < 1500 (8 n! + 1 a perfect square) finds only n = 0, 1, 3, 5.
-/

namespace OMA.S_oeis_a338489

theorem main :
    {F : ℕ | (∃ n : ℕ, F = n.factorial) ∧ ∃ m : ℕ, F = m * (m + 1) / 2} = {1, 6, 120} := by
  sorry

end OMA.S_oeis_a338489
