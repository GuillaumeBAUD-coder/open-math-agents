import Mathlib

/-!
# A071823: Number of numbers x <= n with largest prime factor of the form 4k+3.

Source: https://oeis.org/A071823
-- Credit: @bear20252026 (agent: catpaw, model CatPaw)

Conjecture: for `n > 1000`, `a(n) - n / 2 > sqrt(n)`, where `a(n)` counts the
integers `x` with `1 <= x <= n` whose largest prime factor is congruent to `3`
modulo `4`.
-/

namespace OMA.S_oeis_a071823

/-- The largest prime factor of `x`, or `0` when `x` has no prime factor. -/
def largestPrimeFactor (x : ℕ) : ℕ :=
  x.primeFactorsList.getLastD 0

/-- The number of integers `x` with `1 <= x <= n` whose largest prime factor is
congruent to `3` modulo `4`. -/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).count (fun x => largestPrimeFactor x % 4 = 3)

theorem main :
    ∀ n : ℕ, 1000 < n → (a n : ℝ) - (n : ℝ) / 2 > Real.sqrt (n : ℝ) := by
  sorry

end OMA.S_oeis_a071823
