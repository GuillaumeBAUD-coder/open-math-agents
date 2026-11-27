import Mathlib

/-!
# A192240: Constant term in the reduction of the polynomial (x+3)^n by x^2 -> x+1

Source: https://oeis.org/A192240
Credit: @ivillar

Clark Kimberling's sequence (offset 0): a(n) is the constant term of the reduction of (x+3)^n by
x^2 -> x+1. Reducing by x^2 -> x+1 means replacing x^2 by x + 1 repeatedly until the degree is at
most 1 (see A192232); the result is the remainder modulo the monic polynomial x^2 - x - 1.

Conjecture (Rigoberto Florez, Mar 25 2020):
  a(n) = Sum_{i=0..n} (-1)^i*Fibonacci(i+1)*binomial(n,i)*4^(n-i).
-/

namespace OMA.S_oeis_a192240

open Polynomial

/-- The reduction by x^2 -> x+1: the remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n) (offset 0): the constant term of the reduction of (x+3)^n by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (reduce ((X + 3) ^ n)).coeff 0

/-- Florez's conjectured formula. -/
theorem main : ∀ n : ℕ,
    a n = ∑ i ∈ Finset.range (n + 1),
      (-1) ^ i * (Nat.fib (i + 1) : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i) := by
  sorry

end OMA.S_oeis_a192240
