import Mathlib

/-!
# OEIS A211433: the order-7 recurrence for triples with w + 2x + 4y = 0

Source: https://oeis.org/A211433
Credit: Sudharsan Rajendiran

A211433(n) is the number of ordered triples `(w, x, y)` with all terms in `{-n, ..., 0, ..., n}` and
`w + 2x + 4y = 0`. Colin Barker conjectured (May 2017) the g.f.
`(1 + 5x^2 + 4x^3 + 5x^4 + x^6)/((1 - x)^3 (1 + x)^2 (1 + x^2))` and the recurrence
`a(n) = a(n-1) + a(n-2) - a(n-3) + a(n-4) - a(n-5) - a(n-6) + a(n-7)` for `n > 6`. We state the
recurrence (the g.f. is equivalent to it given the initial terms).

Conventions: offset `0`; the identity is taken in `ℤ`.
-/

namespace OMA.S_oeis_a211433

/-- `{-n, …, 0, …, n}` as a finite set of integers. -/
noncomputable def B (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

/-- A211433(n): the number of ordered triples `(w, x, y)` with all terms in `{-n, …, n}` and
`w + 2x + 4y = 0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((B n ×ˢ B n ×ˢ B n).filter (fun t : ℤ × ℤ × ℤ => t.1 + 2 * t.2.1 + 4 * t.2.2 = 0)).card

theorem main : ∀ n : ℕ, 6 < n →
    (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3) + a (n - 4) - a (n - 5) - a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a211433
