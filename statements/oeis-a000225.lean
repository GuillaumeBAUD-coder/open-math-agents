import Mathlib

/-!
# A000225: a(n) = 2^n - 1. (Sometimes called Mersenne numbers, although that name is usually reserved for A001348.)

Source: https://oeis.org/A000225
Credit: @darealpandaboi

Conjecture (Chai Wah Wu, Sep 08 2021): except for a(2) = 3, the terms of A000225 are the
numbers m such that 2^(m+1) - 2^j - 2^k - 1 is composite for all 0 <= j < k <= m.

Translation notes.
* The terms of A000225 are 2^n - 1 for n >= 0, so they include 0 and 1.
* Composite is read as not prime. The two readings differ only when the value is 0 or 1,
  which happens only for m <= 2: for m >= 3 every value is at least 2^(m-1) - 1 >= 3.
  For m = 1 the only value is 2^2 - 2^0 - 2^1 - 1 = 0, so the strict reading
  (greater than 1 and not prime) would exclude the term a(1) = 1 and make the statement
  false outright, contradicting the data the conjecture was drawn from
  (computing the set with not prime gives 0, 1, 7, 15, 31, 63, 127 for m < 140).
* Natural-number subtraction is exact here: for 0 <= j < k <= m,
  2^j + 2^k + 1 <= 2^(m-1) + 2^m + 1 <= 2^(m+1).
-/

namespace OMA.S_oeis_a000225

theorem main : ∀ m : ℕ, ((∃ n : ℕ, m = 2 ^ n - 1) ∧ m ≠ 3) ↔
    ∀ j k : ℕ, j < k → k ≤ m → ¬ (2 ^ (m + 1) - 2 ^ j - 2 ^ k - 1).Prime := by
  sorry

end OMA.S_oeis_a000225
