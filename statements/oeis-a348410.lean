import Mathlib

/-!
# A348410: solutions of n = Sum (a_i + b_i) with b_i even (Mathar's recurrence)

Source: https://oeis.org/A348410
Credit: @SSmurf

A348410 (offset 0) is the number of nonnegative integer solutions of
`n = Sum_{i=1..n} (a_i + b_i)` with every `b_i` even: 1, 1, 5, 19, 85, 376, 1715, 7890, 36693, ….

The conjecture formalized here (R. J. Mathar, Oct 19 2021, FORMULA section of A348410):

  D-finite with recurrence
  7168*n*(2*n-1)*(n-1)*a(n) - 64*(n-1)*(1759*n^2-5294*n+5112)*a(n-1)
  + 12*(7561*n^3-75690*n^2+165271*n-101070)*a(n-2)
  + 5*(110593*n^3-743946*n^2+1659971*n-1232778)*a(n-3)
  + 2680*(4*n-15)*(2*n-7)*(4*n-13)*a(n-4) = 0.

Formalization notes.
* `a` is defined by the formula of the entry (P. Bala, Feb 21 2022),
  `a(n) = Sum_{k=0..floor(n/2)} binomial(2n-2k-1, n-2k) * binomial(n+k-1, k)`:
  if the `b_i` sum to `2k`, there are `binomial(n+k-1, k)` choices for the `b_i` and
  `binomial(2n-2k-1, n-2k)` choices for the `a_i`, which sum to `n - 2k` (stars and bars).
  The subtractions are truncated subtractions in `ℕ`; they are exact for `n ≥ 1`, and for `n = 0`
  the formula gives `a(0) = 1`, as in the entry.
* The entry gives no range for the recurrence. It fails for `n = 4` with the entry's `a(0) = 1`
  (the left side is then `2010`), and it holds for `5 ≤ n ≤ 69` (checked numerically), so it is
  stated for all `n ≥ 5`. Coefficients and terms are cast to `ℤ`.
-/

namespace OMA.S_oeis_a348410

/-- A348410, by the binomial sum of the entry:
`a(n) = Sum_{k=0..floor(n/2)} binomial(2n-2k-1, n-2k) * binomial(n+k-1, k)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), (2 * n - 2 * k - 1).choose (n - 2 * k) * (n + k - 1).choose k

/-- Mathar's conjectured recurrence, for all `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    7168 * (n : ℤ) * (2 * (n : ℤ) - 1) * ((n : ℤ) - 1) * (a n : ℤ)
      - 64 * ((n : ℤ) - 1) * (1759 * (n : ℤ) ^ 2 - 5294 * (n : ℤ) + 5112) * (a (n - 1) : ℤ)
      + 12 * (7561 * (n : ℤ) ^ 3 - 75690 * (n : ℤ) ^ 2 + 165271 * (n : ℤ) - 101070) * (a (n - 2) : ℤ)
      + 5 * (110593 * (n : ℤ) ^ 3 - 743946 * (n : ℤ) ^ 2 + 1659971 * (n : ℤ) - 1232778) * (a (n - 3) : ℤ)
      + 2680 * (4 * (n : ℤ) - 15) * (2 * (n : ℤ) - 7) * (4 * (n : ℤ) - 13) * (a (n - 4) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a348410
