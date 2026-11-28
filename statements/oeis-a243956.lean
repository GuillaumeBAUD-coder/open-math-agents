import Mathlib

/-!
# OEIS A243956: sums of two members of A002822

Source: https://oeis.org/A243956 (OEIS Foundation, CC BY-SA 4.0).

Entry: Positive numbers n without a decomposition into a sum n = i+j such that
6i-1, 6i+1, 6j-1, 6j+1 are twin primes (data 1, 16, 67, 86, 131, 151, 186,
191, 211, 226, 541, 701).

Conjecture (Lear Young, Jun 15 2014): any integer n > 701 has a decomposition
into a sum n = i+j such that 6i-1, 6i+1, 6j-1, 6j+1 are twin primes.

Formalization notes:
* i and j are positive integers (A002822, numbers m such that 6m-1, 6m+1 are
  twin primes, starts at m = 1). They need not be distinct (e.g. 2 = 1 + 1).
* With i ≥ 1, the natural-number subtraction `6 * i - 1` is the integer 6i - 1.
-/

namespace OMA.S_oeis_a243956

/-- Every integer n > 701 is i + j with i, j ≥ 1 and 6i ± 1, 6j ± 1 all prime. -/
theorem main :
    ∀ n : ℕ, 701 < n →
      ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ i + j = n ∧
        (6 * i - 1).Prime ∧ (6 * i + 1).Prime ∧
        (6 * j - 1).Prime ∧ (6 * j + 1).Prime := by
  sorry

end OMA.S_oeis_a243956
