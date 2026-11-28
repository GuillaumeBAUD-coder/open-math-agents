import Mathlib

/-!
# A309518: Barker's recurrence

Source: https://oeis.org/A309518
Credit: @ivillar

Wesley Ivan Hurt's sequence: the number of even parts in the partitions of n into 4 parts
(offset 0; data 0, 0, 0, 0, 0, 1, 2, 5, 8, 10, 14, ...), with the entry's formula
a(n) = Sum_{k=1..floor(n/4)} Sum_{j=k..floor((n-k)/3)} Sum_{i=j..floor((n-j-k)/2)}
  (((i-1) mod 2) + ((j-1) mod 2) + ((k-1) mod 2) + ((n-i-j-k-1) mod 2)).
Colin Barker conjectured (Aug 06 2019)
a(n) = 3*a(n-1) - 4*a(n-2) + 4*a(n-3) - 4*a(n-4) + 4*a(n-5) - 3*a(n-6) + a(n-7) + a(n-8)
  - 3*a(n-9) + 4*a(n-10) - 4*a(n-11) + 4*a(n-12) - 4*a(n-13) + 3*a(n-14) - a(n-15).

Status: conjecture recorded in the entry (Colin Barker, Aug 06 2019).

Formalization notes:
* The triple sum is the entry's formula; it enumerates the partitions
  k + j + i + (n - i - j - k) of n with 1 <= k <= j <= i <= n - i - j - k, and, as every part
  `x` is at least 1, `(x - 1) % 2` is 1 exactly when `x` is even.
* The entry states no range for the recurrence; it is stated here for every n >= 15, i.e. for
  every n at which all of a(n-1), ..., a(n-15) are defined (offset 0). It is stated over ℤ.
* Barker's generating function
  x^5*(1 - x + 3*x^2 - 3*x^3 + 2*x^4) /
  ((1 - x)^4*(1 + x)*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)*(1 + x^4))
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a309518

/-- A309518: the entry's triple sum counting the even parts of the partitions of `n` into 4
parts. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 4), ∑ j ∈ Finset.Icc k ((n - k) / 3),
    ∑ i ∈ Finset.Icc j ((n - j - k) / 2),
      ((i - 1) % 2 + (j - 1) % 2 + (k - 1) % 2 + (n - i - j - k - 1) % 2)

/-- Barker's conjectured recurrence for A309518, for every `n ≥ 15`. -/
theorem main : ∀ n : ℕ, 14 < n →
    (a n : ℤ) = 3 * a (n - 1) - 4 * a (n - 2) + 4 * a (n - 3) - 4 * a (n - 4) + 4 * a (n - 5) -
      3 * a (n - 6) + a (n - 7) + a (n - 8) - 3 * a (n - 9) + 4 * a (n - 10) - 4 * a (n - 11) +
      4 * a (n - 12) - 4 * a (n - 13) + 3 * a (n - 14) - a (n - 15) := by
  sorry

end OMA.S_oeis_a309518
