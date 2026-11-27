import Mathlib

/-!
# A049997: Numbers of the form Fibonacci(i)*Fibonacci(j)

Source: https://oeis.org/A049997
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A049997): Fibonacci(m)*Fibonacci(n) with 2 < m < n is
a perfect power only for (m,n) = (3,6). This has been verified for 2 < m < n <= 900.

Conventions:
* Fibonacci(m) is Mathlib's `Nat.fib m` (Fibonacci(1) = Fibonacci(2) = 1, Fibonacci(3) = 2).
* A perfect power is x ^ k with x > 1 and k > 1. (OEIS A001597 also lists 1, but for 2 < m < n the
  product is at least Fibonacci(3) * Fibonacci(4) = 6, so the conventions agree here.)
* "is a perfect power only for (m,n) = (3,6)" is stated as an equivalence: for 2 < m < n the product
  is a perfect power if and only if (m, n) = (3, 6), where it equals 2 * 8 = 2^4.
-/

namespace OMA.S_oeis_a049997

/-- `x` is a perfect power: `x = b ^ k` for some natural numbers `b > 1` and `k > 1`. -/
def IsPerfectPower (x : ℕ) : Prop :=
  ∃ b k : ℕ, 1 < b ∧ 1 < k ∧ b ^ k = x

/-- Sun's conjecture on A049997: for `2 < m < n`, `Fibonacci(m) * Fibonacci(n)` is a perfect power
if and only if `(m, n) = (3, 6)`. -/
theorem main : ∀ m n : ℕ, 2 < m → m < n →
    (IsPerfectPower (Nat.fib m * Nat.fib n) ↔ (m = 3 ∧ n = 6)) := by
  sorry

end OMA.S_oeis_a049997
