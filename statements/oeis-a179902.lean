import Mathlib

/-!
# A179902: Row sums of triangle A179901.

Source: https://oeis.org/A179902
Credit: @rickmanelius

Comment in the entry (unsigned; the entry is by Gary W. Adamson, Jul 31 2010): Conjectured mod 2
parity: (1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,...).

Formalization notes:
* A179901 is the triangle read by rows of the antidiagonals of an array generated from
  (1, r, r, r, ...) convolved with (1, 0, r, r, r, ...). Row r ≥ 1 of the array is the coefficient
  sequence of the product of the power series with coefficients (1, r, r, r, ...) (`u r`) and
  (1, 0, r, r, r, ...) (`v r`), with natural number coefficients (`PowerSeries.mk`). Row r begins
  1, r, 2r, 2r + r^2, ..., as in the example section of A179901 (row 1: 1, 1, 2, 3, 4, ...;
  row 2: 1, 2, 4, 8, 12, ...) and its PARI program A(r, n) (n ≥ 1 is the column).
* A(r, k), for k ≥ 1, is the k-th term of row r, that is the coefficient of x^(k-1).
  Row n ≥ 1 of the triangle is the n-th antidiagonal of the array, T(n, k) = A(n + 1 - k, k) for
  k = 1..n, the order of the PARI program (the row sum does not depend on the order).
* a(n) is the sum of row n of the triangle, offset 1. These definitions reproduce the listed terms
  of A179901 (rows 1 to 12), the 42 listed terms 1, 2, 5, 11, 23, ..., 194261, 214882 of A179902
  and the 1000 terms of its b-file (checked by computer).
* The conjectured parity pattern lists a(n) mod 2 for n = 1, 2, 3, ...: the block (1, 0, 1, 1)
  repeats with period 4, so a(n) is even exactly when n == 2 (mod 4). The conjecture is stated
  for every n ≥ 1 (the offset) as a n % 2 = 0 if n % 4 = 2 and a n % 2 = 1 otherwise. For n = 0,
  outside the offset, a is an empty sum; n = 0 is excluded.
-/

namespace OMA.S_oeis_a179902

/-- The sequence (1, r, r, r, ...): the coefficient of x^0 is 1, every other coefficient is r. -/
def u (r i : ℕ) : ℕ := if i = 0 then 1 else r

/-- The sequence (1, 0, r, r, r, ...): coefficient 1 at x^0, 0 at x^1, and r from x^2 on. -/
def v (r j : ℕ) : ℕ := if j = 0 then 1 else if j = 1 then 0 else r

/-- Row r of the array of A179901 as a power series: (1, r, r, ...) convolved with
(1, 0, r, r, ...). -/
noncomputable def row (r : ℕ) : PowerSeries ℕ := PowerSeries.mk (u r) * PowerSeries.mk (v r)

/-- A(r, k): the k-th term (k ≥ 1) of row r of the array, the coefficient of x^(k-1). -/
noncomputable def A (r k : ℕ) : ℕ := PowerSeries.coeff (k - 1) (row r)

/-- T(n, k) of A179901 for 1 ≤ k ≤ n: the n-th antidiagonal of the array. -/
noncomputable def T (n k : ℕ) : ℕ := A (n + 1 - k) k

/-- A179902(n) for n ≥ 1: the sum of row n of the triangle A179901. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, T n k

/-- The conjecture: for n ≥ 1, a(n) mod 2 follows the pattern 1, 0, 1, 1, 1, 0, 1, 1, ...,
that is a(n) is even if and only if n == 2 (mod 4). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n % 2 = if n % 4 = 2 then 0 else 1 := by
  sorry

end OMA.S_oeis_a179902
