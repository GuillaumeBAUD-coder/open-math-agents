import Mathlib.Data.Nat.Fib.Basic

/-!
# A163250: a(n) = A000045(n+6) - (n^2 + 4*n + 8).

Source: https://oeis.org/A163250
Credit: @vivanpoddar

The sequence (offset 0) is 0, 0, 1, 5, 15, 36, 76, 148, 273, ..., where A000045 are the Fibonacci
numbers with F(0) = 0, F(1) = 1.

The conjecture (Bill McEachen, Jan 20 2023) reads
a(n) = (n-1)^2 + a(n-1) + a(n-2), n > 2.
-/

namespace OMA.S_oeis_a163250

/-- A163250 (offset 0): a(n) = Fibonacci(n+6) - (n^2 + 4*n + 8). -/
def a (n : ℕ) : ℤ :=
  (Nat.fib (n + 6) : ℤ) - ((n : ℤ) ^ 2 + 4 * (n : ℤ) + 8)

/-- The conjectured recurrence for A163250. -/
theorem main : ∀ n : ℕ, 2 < n → a n = ((n : ℤ) - 1) ^ 2 + a (n - 1) + a (n - 2) := by
  sorry

end OMA.S_oeis_a163250
