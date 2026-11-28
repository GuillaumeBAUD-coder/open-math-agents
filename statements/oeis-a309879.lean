import Mathlib

/-!
# A309879: Barker's recurrence

Source: https://oeis.org/A309879
Credit: @ivillar

Wesley Ivan Hurt's sequence: the number of odd parts appearing among the fourth largest parts of the
partitions of n into 5 parts
(offset 0; data 0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 7, ...), with the entry's formula
a(n) = Sum_{l=1..floor(n/5)} Sum_{k=l..floor((n-l)/4)} Sum_{j=k..floor((n-k-l)/3)}
  Sum_{i=j..floor((n-j-k-l)/2)} (k mod 2).
Colin Barker conjectured (Aug 22 2019)
a(n) = 2*a(n-1) - a(n-2) + a(n-3) - 2*a(n-4) + a(n-5) + a(n-8) - 2*a(n-9) + 2*a(n-10) -
  3*a(n-11) + 3*a(n-12) - 2*a(n-13) + 2*a(n-14) - a(n-15) - a(n-18) + 2*a(n-19) - a(n-20) +
  a(n-21) - 2*a(n-22) + a(n-23) for n > 22.

Status: known result; the entry records that Barker's conjectures were verified by Wesley Ivan
Hurt (Aug 24 2019), and it also gives a closed form due to Hoang Xuan Thanh.

Formalization notes:
* The quadruple sum is the entry's formula; it enumerates the partitions
  l + k + j + i + (n - i - j - k - l) of n with 1 <= l <= k <= j <= i <= n - i - j - k - l, and the
  summand is `k % 2`, which is 1 exactly when the fourth largest part `k` is odd.
* The recurrence is stated over ℤ.
* Barker's generating function
  x^5*(1 - x + x^2)*(1 - x^3 + x^6) / ((1 - x)^5*(1 + x)^2*(1 + x^2)*(1 + x + x^2)*
  (1 - x + x^2 - x^3 + x^4)*(1 + x^4)*(1 + x + x^2 + x^3 + x^4))
  is the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a309879

/-- A309879: the entry's quadruple sum over the partitions of `n` into 5 parts. -/
def a (n : ℕ) : ℕ :=
  ∑ l ∈ Finset.Icc 1 (n / 5), ∑ k ∈ Finset.Icc l ((n - l) / 4),
    ∑ j ∈ Finset.Icc k ((n - k - l) / 3), ∑ i ∈ Finset.Icc j ((n - j - k - l) / 2), k % 2

/-- Barker's recurrence for A309879 (verified by Hurt), for every `n > 22`. -/
theorem main : ∀ n : ℕ, 22 < n →
    (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 3) - 2 * a (n - 4) + a (n - 5) + a (n - 8)
      - 2 * a (n - 9) + 2 * a (n - 10) - 3 * a (n - 11) + 3 * a (n - 12) - 2 * a (n - 13)
      + 2 * a (n - 14) - a (n - 15) - a (n - 18) + 2 * a (n - 19) - a (n - 20) + a (n - 21)
      - 2 * a (n - 22) + a (n - 23) := by
  sorry

end OMA.S_oeis_a309879
