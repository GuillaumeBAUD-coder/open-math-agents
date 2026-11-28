import Mathlib

/-!
# A334995: Twice the area of triangle with coordinates (Fn, Fn+k), (Fn+2k, Fn+3k) and (Fn+4k, Fn+5k), where Fn is the n-th Fibonacci number A000045.

Source: https://oeis.org/A334995
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data 1, 15, 256, 2835, 33275, 368640, 4121741, 45703035, ...) records in
its FORMULA section:

  Conjectures from Colin Barker, May 19 2020:
  G.f.: x*(1 + x^2)*(1 + 5*x + 74*x^2 - 5*x^3 + x^4) / ((1 + 4*x - x^2)*(1 + x - x^2)*(1 - 4*x - x^2)*(1 - 11*x - x^2)).
  a(n) = 10*a(n-1) + 31*a(n-2) - 190*a(n-3) - 236*a(n-4) + 190*a(n-5) + 31*a(n-6)- 10*a(n-7) - a(n-8) for n>8.

Conventions:
* The sequence is indexed from `1`, as in the entry; `a 0` is also defined (it is `0`) but the
  statement only uses `a n` with `n ≥ 1`.
* `F m` is the Fibonacci number `Nat.fib m` (A000045: F(0) = 0, F(1) = 1), viewed in `ℤ`.
* In the name, `Fn+k` means F(n+k), and the step `k` equals the index `n` (the name leaves `k`
  implicit; this is the reading that reproduces the data: for n = 2 the points are
  (1, 3), (8, 21), (55, 144), with twice the area 15). So the vertices of the n-th triangle are
  (F(n), F(n+n)), (F(n+2n), F(n+3n)) and (F(n+4n), F(n+5n)).
* Twice the area of the triangle with vertices (x1, y1), (x2, y2), (x3, y3) is the absolute value
  of the determinant (x2 - x1)*(y3 - y1) - (x3 - x1)*(y2 - y1) (shoelace formula).
* Only the recurrence is formalized; together with the initial terms a(1), ..., a(8) it is
  equivalent to the stated g.f. The recurrence is stated in `ℤ` for every `n ≥ 9` (that is,
  `n > 8`).
-/

namespace OMA.S_oeis_a334995

/-- The Fibonacci number `F(m)` (A000045), as an integer. -/
def F (m : ℕ) : ℤ := (Nat.fib m : ℤ)

/-- Twice the area of the triangle with vertices `(x1, y1)`, `(x2, y2)`, `(x3, y3)`. -/
def twiceArea (x1 y1 x2 y2 x3 y3 : ℤ) : ℕ :=
  Int.natAbs ((x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1))

/-- A334995: twice the area of the triangle with vertices `(F(n), F(n+k))`,
`(F(n+2k), F(n+3k))`, `(F(n+4k), F(n+5k))`, where `k = n`. -/
def a (n : ℕ) : ℕ :=
  twiceArea (F n) (F (n + n)) (F (n + 2 * n)) (F (n + 3 * n)) (F (n + 4 * n)) (F (n + 5 * n))

/-- Colin Barker's conjecture: for `n > 8`, a(n) = 10*a(n-1) + 31*a(n-2) - 190*a(n-3)
- 236*a(n-4) + 190*a(n-5) + 31*a(n-6) - 10*a(n-7) - a(n-8). -/
theorem main : ∀ n : ℕ, 9 ≤ n →
    (a n : ℤ) = 10 * a (n - 1) + 31 * a (n - 2) - 190 * a (n - 3) - 236 * a (n - 4)
      + 190 * a (n - 5) + 31 * a (n - 6) - 10 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a334995
