import Mathlib

/-!
# A075362 / A023855: Antidiagonal sums.

Source: https://oeis.org/A075362 and https://oeis.org/A023855
Name: Triangle read by rows with the n-th row containing the first n
multiples of n.
Conjecture (L. Edson Jeffery, Jan 20 2012): the antidiagonal sums of this
triangle are A023855.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

The triangle has entry `n * k` in row `n`, column `k` (`1 <= k <= n`).
The `m`-th antidiagonal consists of the cells with `n + k = m`; the
condition `k <= n` restricts it to `k <= m/2`, so its sum is
`Sum_{k < m, 2*k <= m} (m - k) * k`.  We compare this with A023855, whose
`n`-th term (`n >= 1`) is `(n+1)*(n+3)*(2*n+1)/24` for odd `n` and
`n*(n+1)*(n+2)/12` for even `n`; the first antidiagonal corresponds to
`n = 1`.  An independent calculation checks the two sides for all
`m <= 2000`.  The body stays `sorry`; a person reviews the translation
before merging.
-/

namespace OMA.S_oeis_a075362

/-- Entry in row `n`, column `k` of the triangle: the `k`-th multiple of `n`. -/
def tri (n k : ℕ) : ℕ := n * k

/-- Sum of the entries on the antidiagonal `n + k = m` of the triangle. -/
def antidiag (m : ℕ) : ℕ :=
  (Finset.range m).sum
    (fun k => if 2 * k ≤ m then tri (m - k) k else 0)

/-- A023855, starting at `n = 1`: total areas of rectangles of perimeter `2n`. -/
def a023855 (n : ℕ) : ℕ :=
  if n % 2 = 1 then (n + 1) * (n + 3) * (2 * n + 1) / 24
  else n * (n + 1) * (n + 2) / 12

theorem main :
    ∀ n : ℕ, 1 ≤ n → antidiag (n + 1) = a023855 n := by
  sorry

end OMA.S_oeis_a075362
