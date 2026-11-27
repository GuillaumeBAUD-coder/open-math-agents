import Mathlib

/-!
# A192754: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192754
Credit: @JeremyDevs

Formalizes the closed form conjectured in OEIS A192754 (R. J. Mathar, May 04 2014):
a(n) = A000071(n+3) + 4*A000071(n+2).

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + 5*n+1 for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`,
  with the recursion written with `n + 1` in place of `n`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its constant term is its coefficient of index 0.
* The sequence has offset 0 and a(n) is the constant term of the reduction of p(n,x)
  (data 1, 6, 12, 23, 40, 68, ...; for instance p(1,x) = x + 6 -> 6 + x, p(2,x) = x^2 + 6x + 11 -> 12 + 7x).
* A000071(n) = Fibonacci(n) - 1 (the name of that entry), with Fibonacci(0) = 0,
  Fibonacci(1) = 1: here `(Nat.fib n : ℤ) - 1`.
* The closed form is asserted for every `n ≥ 0`, the full range of the offset-0 sequence.
* The same comment also records "G.f.: ( 1+4*x ) / ( (x-1)*(x^2+x-1) ), partial sums of A022095".
  These are not stated separately: the generating function is the one of the closed form.
-/

namespace OMA.S_oeis_a192754

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + 5*n+1. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C (5 * ((n : ℤ) + 1) + 1)

/-- A192754 (offset 0): the constant term of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 0

/-- For every `n`, a(n) = A000071(n+3) + 4*A000071(n+2). -/
theorem main : ∀ n : ℕ,
    a n = ((Nat.fib (n + 3) : ℤ) - 1) + 4 * ((Nat.fib (n + 2) : ℤ) - 1) := by
  sorry

end OMA.S_oeis_a192754
