import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Defs

open scoped BigOperators

namespace OMA.S_oeis_a007223

/-- Number of distinct perforation patterns for deriving `(n+2, n)` punctured convolutional
codes from `(2, 1)`: `(1/n) * ∑_{k ∣ gcd(n+2, n)} φ(k) * C(2n/k, (n+2)/k)`. -/
def a007223 (n : ℕ) : ℚ :=
  (∑ k ∈ (Nat.gcd (n + 2) n).divisors,
      (Nat.totient k * Nat.choose (2 * n / k) ((n + 2) / k) : ℚ)) / (n : ℚ)

/-- Coefficient of `x^n` in `(A(x)^2 + A(x^2)) / 2`, where `A(x) = ∑_{k ≥ 1} C_k x^k`. -/
def catalanConj (n : ℕ) : ℚ :=
  ((∑ k ∈ Finset.Icc 1 (n - 1), (catalan k : ℚ) * (catalan (n - k) : ℚ)) +
    if 2 ∣ n then (catalan (n / 2) : ℚ) else 0) / 2

/-- OEIS A007223 (R. J. Mathar conjecture): for every `n ≥ 1`, `a(n)` equals the `x^n`
coefficient of `(A(x)^2 + A(x^2)) / 2`, where `A(x) = A000108(x) - 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a007223 n = catalanConj n := by
  sorry

end OMA.S_oeis_a007223
