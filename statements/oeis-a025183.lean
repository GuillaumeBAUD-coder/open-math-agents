import Mathlib

/-!
# A025183: T(2n-1, n), T given by A025177 (Mathar's recurrence)

Source: https://oeis.org/A025183 (array: https://oeis.org/A025177)
Credit: @SSmurf

A025177 is the array of first differences in the `(n, n)` direction of the trinomial array
A027907 (generating function `(1 - y z) / (1 - z (1 + y + y^2))`); it satisfies
`T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)`, starting with the rows `[1]` and `[1, 0, 1]`.

A025183 (offset 1) is `a(n) = T(2n-1, n)`: 0, 4, 20, 111, 616, 3465, 19668, 112476, ….

The conjecture formalized here (R. J. Mathar, Feb 25 2015, FORMULA section of A025183):

  9*n*(10833*n-26779)*(3*n-4)*(3*n-2)*a(n)
  - 3*(n-1)*(749757*n^3+509641*n^2-11324756*n+13648560)*a(n-1)
  - 2*(2*n-5)*(4152209*n^3-25903434*n^2+56589136*n-40818816)*a(n-2)
  - 36*(n-3)*(85207*n-129510)*(2*n-5)*(2*n-7)*a(n-3) = 0.

Formalization notes.
* `T` is the definition used in the merged statements of A025184 and A025187: the recursion with
  the two initial rows given in A025177; the terms with `k - 1 < 0` or `k - 2 < 0` are omitted.
* The offset is 1, so the recurrence is stated for every `n` for which all four terms lie in the
  sequence, i.e. `n ≥ 4`. Terms and coefficients are in `ℤ`.
* With the definition below `a(1), a(2), …` are 0, 4, 20, 111, 616, 3465, as in the entry, and the
  recurrence was checked numerically for `4 ≤ n ≤ 58`.
-/

namespace OMA.S_oeis_a025183

/-- A025177: `T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)`, starting with the rows `[1]` and
`[1, 0, 1]`. Entries with `k < 0` are absent (they are `0`). -/
def T : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 ∨ k = 2 then 1 else 0
  | n + 2, k => T (n + 1) k + (if 1 ≤ k then T (n + 1) (k - 1) else 0) +
      (if 2 ≤ k then T (n + 1) (k - 2) else 0)

/-- A025183: `a(n) = T(2n-1, n)` for `n ≥ 1`. -/
def a (n : ℕ) : ℤ := T (2 * n - 1) n

/-- Mathar's conjectured recurrence, for all `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    9 * (n : ℤ) * (10833 * (n : ℤ) - 26779) * (3 * (n : ℤ) - 4) * (3 * (n : ℤ) - 2) * a n
      - 3 * ((n : ℤ) - 1) * (749757 * (n : ℤ) ^ 3 + 509641 * (n : ℤ) ^ 2 - 11324756 * (n : ℤ) + 13648560) * a (n - 1)
      - 2 * (2 * (n : ℤ) - 5) * (4152209 * (n : ℤ) ^ 3 - 25903434 * (n : ℤ) ^ 2 + 56589136 * (n : ℤ) - 40818816) * a (n - 2)
      - 36 * ((n : ℤ) - 3) * (85207 * (n : ℤ) - 129510) * (2 * (n : ℤ) - 5) * (2 * (n : ℤ) - 7) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025183
