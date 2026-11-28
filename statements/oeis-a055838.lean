import Mathlib

/-!
# A055838: T(2n+4, n), T given by A055830 (Mathar's recurrence)

Source: https://oeis.org/A055838 (triangle: https://oeis.org/A055830)
Credit: @SSmurf

The triangle A055830 (Kimberling; diagonal differences of A037027) is given in its FORMULA section
(Philippe Deléham, Nov 05 2006) by
`T(n,k) = 0 if k > n or if k < 0, T(0,0) = 1, T(1,1) = 0, T(n,k) = T(n-1,k-1) + T(n-1,k) + T(n-2,k)`.
It begins 1; 1, 0; 2, 1, 0; 3, 3, 1, 0; 5, 7, 4, 1, 0; 8, 15, 12, 5, 1, 0.

A055838 (offset 0) is `a(n) = T(2n+4, n)`: 5, 30, 162, 850, 4425, 22995, 119560, ….

The conjecture formalized here (R. J. Mathar, Mar 13 2016, FORMULA section of A055838):

  5*n*(n+3)*(n-1)*a(n) - 2*(n-1)*(11*n+8)*(n+2)*a(n-1) - 3*(3*n-1)*(3*n-2)*(n+1)*a(n-2) = 0.

Formalization notes.
* `T` is defined by the recursion above with rows 0 and 1 equal to `1` and `1, 0`; terms with a
  negative column index are omitted, and `T(n,k) = 0` for `k > n` then follows from the recursion.
* The recurrence is stated for every `n` for which all three terms are in the sequence, i.e.
  `n ≥ 2`. Terms and coefficients are in `ℤ`.
* With the definition below `a` starts 5, 30, 162, 850, 4425, 22995, 119560, as in the entry, and the
  recurrence was checked numerically for `2 ≤ n ≤ 59`.
-/

namespace OMA.S_oeis_a055838

/-- Kimberling's triangle A055830. -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 then 1 else 0
  | n + 2, k => (if 1 ≤ k then T (n + 1) (k - 1) else 0) + T (n + 1) k + T n k

/-- A055838: `a(n) = T(2n+4, n)`. -/
def a (n : ℕ) : ℤ := (T (2 * n + 4) n : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    5 * (n : ℤ) * ((n : ℤ) + 3) * ((n : ℤ) - 1) * a n
      - 2 * ((n : ℤ) - 1) * (11 * (n : ℤ) + 8) * ((n : ℤ) + 2) * a (n - 1)
      - 3 * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) - 2) * ((n : ℤ) + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a055838
