import Mathlib

/-!
# A090826: Convolution of Catalan and Fibonacci numbers.

Source: https://oeis.org/A090826
Credit: @vivanpoddar

The sequence (offset 0) is 0, 1, 2, 5, 12, 31, 85, 248, ...: the convolution CONV(A000045, A000108),
a(n) = Sum_{k=0..n} Fibonacci(k) * Catalan(n-k), with Fibonacci(0) = 0 and Catalan(0) = 1.

The conjecture (R. J. Mathar, Jul 09 2013) reads
n*a(n) + (-5*n+6)*a(n-1) + 3*(n-2)*a(n-2) + 2*(2*n-3)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3, over the integers.
-/

namespace OMA.S_oeis_a090826

/-- A090826 (offset 0): a(n) = Sum_{k=0..n} Fibonacci(k) * Catalan(n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.fib k : ℤ) * (catalan (n - k) : ℤ)

/-- Mathar's conjectured recurrence for A090826. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * a n + (-5 * (n : ℤ) + 6) * a (n - 1) + 3 * ((n : ℤ) - 2) * a (n - 2)
      + 2 * (2 * (n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a090826
