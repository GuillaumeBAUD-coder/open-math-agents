import Mathlib

/-!
# A307872: Barker's recurrence

Source: https://oeis.org/A307872
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the smallest parts in the partitions of n into 3 parts,
a(n) = Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)} k (offset 1; data 0, 0, 1, 1, 2, 4, 5, 7, 11,
13, ...). Colin Barker conjectured (May 02 2019)
a(n) = a(n-1) + a(n-2) + a(n-3) - 2*a(n-4) - 2*a(n-5) + a(n-6) + a(n-7) + a(n-8) - a(n-9) for n > 9.

Status: conjecture recorded in the entry (Wesley Ivan Hurt later added a closed form, Oct 24 2021).

Formalization notes:
* The double sum is the entry's formula; the recurrence is stated over ℤ.
* Barker's generating function x^3 / ((1 - x)^4*(1 + x)*(1 + x + x^2)^2) is the rational function
  determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a307872

/-- A307872: `a(n) = Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)} k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 (n / 3), ∑ _i ∈ Finset.Icc k ((n - k) / 2), k

/-- Barker's conjectured recurrence for A307872, for every `n > 9`. -/
theorem main : ∀ n : ℕ, 9 < n →
    (a n : ℤ) = a (n - 1) + a (n - 2) + a (n - 3) - 2 * a (n - 4) - 2 * a (n - 5) + a (n - 6) +
      a (n - 7) + a (n - 8) - a (n - 9) := by
  sorry

end OMA.S_oeis_a307872
