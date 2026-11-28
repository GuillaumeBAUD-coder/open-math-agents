import Mathlib

/-!
# A002062: a(n) = Fibonacci(n) + n.

Source: https://oeis.org/A002062
Credit: @MartinFoxy

The entry carries the comment (Creighton Dement, Nov 19 2004): with `_x` the offset of each
sequence, `a(n+2)_0 = A006355(n+4)_0 - A066982(n+1)_1 (conjecture)`.

Formalization notes:
* `A002062` has offset 0 and is defined by its name, `a(n) = Fibonacci(n) + n`
  (data: 0, 2, 3, 5, 7, 10, 14, 20, ...).
* `A006355` has offset 0 (number of binary vectors of length `n` containing no singletons).
  It is given here by the closed form recorded in its OEIS entry (Mircea Merca, Jun 28 2012):
  `a(0) = 1` and `a(n) = 2 * Fibonacci(n-1)` for `n > 0` (data: 1, 0, 2, 2, 4, 6, 10, 16, ...).
* `A066982` has offset 1 and is defined by its name, `a(n) = Lucas(n+1) - (n+1)`, with the
  Lucas numbers `L(0) = 2`, `L(1) = 1`, `L(n+2) = L(n+1) + L(n)` (data from n = 1:
  1, 1, 3, 6, 12, 22, 39, ...). It is computed in `ℤ`; the index 0, outside the OEIS offset,
  is never used by the statement, whose smallest index is `n + 1 = 1`.
* The subscripts `_0`, `_0`, `_1` in the comment are the offsets above, so the indices are the
  OEIS indices of each sequence. The identity is stated in `ℤ` for every `n ≥ 0`.
* The second half of the comment (a `seq` expression in Dement's floretion notation) is not a
  conjecture and is not formalized.
-/

namespace OMA.S_oeis_a002062

/-- A002062 (offset 0): `a(n) = Fibonacci(n) + n`. -/
def A002062 (n : ℕ) : ℕ := Nat.fib n + n

/-- A006355 (offset 0): `a(0) = 1` and `a(n) = 2 * Fibonacci(n - 1)` for `n > 0`. -/
def A006355 : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * Nat.fib n

/-- The Lucas numbers A000032: `L(0) = 2`, `L(1) = 1`, `L(n+2) = L(n+1) + L(n)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- A066982 (offset 1): `a(n) = Lucas(n+1) - (n+1)`. -/
def A066982 (n : ℕ) : ℤ := (lucas (n + 1) : ℤ) - ((n : ℤ) + 1)

/-- Creighton Dement's conjecture on A002062 (OEIS Comments section):
`a(n+2) = A006355(n+4) - A066982(n+1)` for every `n ≥ 0`. -/
theorem main : ∀ n : ℕ,
    (A002062 (n + 2) : ℤ) = (A006355 (n + 4) : ℤ) - A066982 (n + 1) := by
  sorry

end OMA.S_oeis_a002062
