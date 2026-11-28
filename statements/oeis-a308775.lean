import Mathlib

/-!
# A308775: Barker's recurrence

Source: https://oeis.org/A308775
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of all the parts in the partitions of n into 4 parts
(offset 0; data 0, 0, 0, 0, 4, 5, 12, 21, 40, 54, 90, ...), i.e. a(n) = n * A026810(n). Colin Barker
conjectured (Jun 24 2019)
a(n) = a(n-2) + 2*a(n-3) + 2*a(n-4) - 2*a(n-5) - 3*a(n-6) - 4*a(n-7) + 4*a(n-9) + 3*a(n-10)
  + 2*a(n-11) - 2*a(n-12) - 2*a(n-13) - a(n-14) + a(n-16) for n > 15.

Status: conjecture recorded in the entry (Colin Barker, Jun 24 2019).

Formalization notes:
* The partitions of n into 4 parts are enumerated as in the entry's Mathematica program:
  k + j + i + (n - i - j - k) with 1 <= k <= j <= i <= n - i - j - k, i.e. k in [1, floor(n/4)],
  j in [k, floor((n - k)/3)] and i in [j, floor((n - j - k)/2)]; the summand is the sum of the
  four parts.
* The recurrence is stated over ℤ.
* Barker's generating function
  x^4*(4 + 5*x + 8*x^2 + 8*x^3 + 10*x^4 + 7*x^5 + 6*x^6) /
  ((1 - x)^5*(1 + x)^3*(1 + x^2)^2*(1 + x + x^2)^2)
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a308775

/-- A308775: the sum of all the parts over the partitions `k + j + i + (n - i - j - k)` of `n`
with `1 ≤ k ≤ j ≤ i ≤ n - i - j - k`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 4), ∑ j ∈ Finset.Icc k ((n - k) / 3),
    ∑ i ∈ Finset.Icc j ((n - j - k) / 2), (k + j + i + (n - i - j - k))

/-- Barker's conjectured recurrence for A308775, for every `n > 15`. -/
theorem main : ∀ n : ℕ, 15 < n →
    (a n : ℤ) = a (n - 2) + 2 * a (n - 3) + 2 * a (n - 4) - 2 * a (n - 5) - 3 * a (n - 6) -
      4 * a (n - 7) + 4 * a (n - 9) + 3 * a (n - 10) + 2 * a (n - 11) - 2 * a (n - 12) -
      2 * a (n - 13) - a (n - 14) + a (n - 16) := by
  sorry

end OMA.S_oeis_a308775
