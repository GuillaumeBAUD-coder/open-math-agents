import Mathlib

/-!
# A309516: Barker's recurrence

Source: https://oeis.org/A309516
Credit: @ivillar

Wesley Ivan Hurt's sequence: the number of odd parts in the partitions of n into 4 parts
(offset 0; data 0, 0, 0, 0, 4, 3, 6, 7, 12, 14, 22, ...), with the entry's formula
a(n) = Sum_{k=1..floor(n/4)} Sum_{j=k..floor((n-k)/3)} Sum_{i=j..floor((n-j-k)/2)}
  ((i mod 2) + (j mod 2) + (k mod 2) + ((n-i-j-k) mod 2)).
Colin Barker conjectured (Aug 06 2019)
a(n) = 2*a(n-1) - a(n-2) + a(n-6) - 2*a(n-7) + 2*a(n-8) - 2*a(n-9) + a(n-10) - a(n-14)
  + 2*a(n-15) - a(n-16) for n > 15.

Status: conjecture recorded in the entry (Colin Barker, Aug 06 2019).

Formalization notes:
* The triple sum is the entry's formula; it enumerates the partitions
  k + j + i + (n - i - j - k) of n with 1 <= k <= j <= i <= n - i - j - k, and `x % 2` is 1
  exactly when the part `x` is odd.
* The recurrence is stated over ℤ.
* Barker's generating function
  x^4*(4 - 5*x + 4*x^2 - 2*x^3 + 4*x^4 - 3*x^5 + 2*x^6) /
  ((1 - x)^4*(1 + x)^2*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)*(1 + x^4))
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a309516

/-- A309516: the entry's triple sum counting the odd parts of the partitions of `n` into 4 parts. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 4), ∑ j ∈ Finset.Icc k ((n - k) / 3),
    ∑ i ∈ Finset.Icc j ((n - j - k) / 2), (i % 2 + j % 2 + k % 2 + (n - i - j - k) % 2)

/-- Barker's conjectured recurrence for A309516, for every `n > 15`. -/
theorem main : ∀ n : ℕ, 15 < n →
    (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 6) - 2 * a (n - 7) + 2 * a (n - 8) -
      2 * a (n - 9) + a (n - 10) - a (n - 14) + 2 * a (n - 15) - a (n - 16) := by
  sorry

end OMA.S_oeis_a309516
