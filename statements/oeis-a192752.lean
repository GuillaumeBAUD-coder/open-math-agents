import Mathlib

/-!
# A192752: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments

Source: https://oeis.org/A192752
Credit: @ivillar

Clark Kimberling's sequence (offset 0): the polynomial p(n,x) is defined recursively by
p(n,x) = x*p(n-1,x) + 4n + 3 for n > 0, with p(0,x) = 1 (the comment writes x*(n-1,x) for
x*p(n-1,x), as the Mathematica program confirms). Reducing by x^2 -> x+1 means replacing x^2 by
x + 1 repeatedly until the degree is at most 1 (see A192232 and A192744); the result is the
remainder of p(n,x) on division by the monic polynomial x^2 - x - 1. a(n) is its constant term.

Conjecture (R. J. Mathar, May 04 2014):
  G.f.: ( 1+5*x-2*x^2 ) / ( (x-1)*(x^2+x-1) ).
  a(n) = A000071(n+3)+5*A000071(n+2) -2*A000071(n+1) and first differences in A022136.
Here A000071(m) = Fibonacci(m) - 1 and A022136 is the Fibonacci sequence beginning 5, 11
(offset 0). The sequence starts 1, 7, 12, 23, 39, 66, ..., with first differences
6, 5, 11, 16, 27, ...: after the first one they run through A022136, i.e.
a(n+1) - a(n) = A022136(n-1) for n ≥ 1, which is how the last claim is stated.
-/

namespace OMA.S_oeis_a192752

open Polynomial

/-- p(0,x) = 1 and p(n,x) = x*p(n-1,x) + 4*n + 3 for n > 0. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C (4 * ((n : ℤ) + 1) + 3)

/-- The reduction of a polynomial by x^2 -> x+1: its remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n): the constant term of the reduction of p(n,x) by x^2 -> x+1 (offset 0). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p n)).coeff 0

/-- A000071: a(n) = Fibonacci(n) - 1. -/
def A000071 (n : ℕ) : ℤ := Nat.fib n - 1

/-- A022136: Fibonacci sequence beginning 5, 11 (offset 0). -/
def A022136 : ℕ → ℕ
  | 0 => 5
  | 1 => 11
  | n + 2 => A022136 (n + 1) + A022136 n

/-- The conjectured g.f. (1+5*x-2*x^2) / ((x-1)*(x^2+x-1)), as a power series over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (1 + 5 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
    ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1))⁻¹

/-- Mathar's conjecture: the g.f., the A000071 formula, and the first differences
a(n+1) - a(n) = A022136(n-1) for n ≥ 1. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) = G ∧
    (∀ n : ℕ, a n = A000071 (n + 3) + 5 * A000071 (n + 2) - 2 * A000071 (n + 1)) ∧
    (∀ n : ℕ, 1 ≤ n → a (n + 1) - a n = A022136 (n - 1)) := by
  sorry

end OMA.S_oeis_a192752
