import Mathlib

/-!
# A217471: Partial sum of fifth power of the even-indexed Fibonacci numbers

Source: https://oeis.org/A217471
Credit: @xor2k

Formalizes the OEIS A217471 formula stated as an example of Melham's conjecture
(offset 0): a(n) = (F(2*n+1)-1)^2*(4*F(2*n+1)^3 + 8*F(2*n+1)^2 - 3*F(2*n+1) - 14)/44.

Conventions: `a n = Sum_{k=0..n} F(2*k)^5` as in the OEIS formula section, with `F = Nat.fib`
(`F 0 = 0`, `F 1 = 1`). The right-hand side is evaluated in `ℚ`, so the subtraction and the
division by `44` are exact (no truncation, no floor).
-/

namespace OMA.S_oeis_a217471

/-- `a n = Sum_{k=0..n} F(2*k)^5`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.fib (2 * k)) ^ 5

/-- For every `n ≥ 0`, `a(n) = (F(2n+1)-1)^2 (4F(2n+1)^3 + 8F(2n+1)^2 - 3F(2n+1) - 14)/44`. -/
theorem main :
    ∀ n : ℕ, (a n : ℚ) =
      ((Nat.fib (2 * n + 1) : ℚ) - 1) ^ 2 *
        (4 * (Nat.fib (2 * n + 1) : ℚ) ^ 3 + 8 * (Nat.fib (2 * n + 1) : ℚ) ^ 2
          - 3 * (Nat.fib (2 * n + 1) : ℚ) - 14) / 44 := by
  sorry

end OMA.S_oeis_a217471
