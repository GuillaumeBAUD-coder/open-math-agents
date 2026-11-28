import Mathlib

/-!
# A203157: (n-1)-st elementary symmetric function of the first n triangular numbers.

Source: https://oeis.org/A203157
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 4, 27, 288, 4500, 97200, 2778300, 101606400, ...
It is defined as in the name of the entry: a(n) is the (n-1)-st elementary symmetric function of
the triangular numbers 1, 3, 6, ..., n*(n+1)/2. Below the terms are indexed from 0 (x 0 = 1 is the
first triangular number) and Mathlib's Multiset.esymm is used.

Conjecture (R. J. Mathar, Oct 01 2016): 2*(-n+1)*a(n) + n^3*a(n-1) = 0.
It involves a(n-1) and the offset is 1, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a203157

/-- The triangular numbers 1, 3, 6, 10, ..., indexed from 0. -/
def x (i : ℕ) : ℤ := (((i + 1) * (i + 2) / 2 : ℕ) : ℤ)

/-- A203157: the (n-1)-st elementary symmetric function of the first n triangular numbers. -/
def a (n : ℕ) : ℤ := ((Multiset.range n).map x).esymm (n - 1)

/-- The conjectured recurrence for A203157. -/
theorem main : ∀ n : ℕ, 2 ≤ n → 2 * (-(n : ℤ) + 1) * a n + (n : ℤ) ^ 3 * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a203157
