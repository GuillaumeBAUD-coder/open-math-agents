import Mathlib

/-!
# A207262: a(n) = 2^(4n - 2) + 1.

Source: https://oeis.org/A207262
Credit: @agchua

Ivan N. Ianakiev (Jan 29 2020), in the comments of A207262:
  Conjecture: Let m = 4n - 2. a(n) equals the sum of the m-th powers of the divisors of m divided
  by the sum of the m-th powers of the odd divisors of m.
The sequence has offset 1, so the conjecture is stated for n ≥ 1 (then m = 4n - 2 ≥ 2). The
divisors are the positive divisors (Nat.divisors), and the quotient is taken in ℚ.
-/

namespace OMA.S_oeis_a207262

/-- A207262(n) = 2^(4n - 2) + 1. -/
def a (n : ℕ) : ℕ := 2 ^ (4 * n - 2) + 1

/-- Ianakiev's conjecture: for m = 4n - 2, a(n) = (Sum_{d | m} d^m) / (Sum_{d | m, d odd} d^m). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = ((∑ d ∈ Nat.divisors (4 * n - 2), d ^ (4 * n - 2) : ℕ) : ℚ)
      / ((∑ d ∈ (Nat.divisors (4 * n - 2)).filter Odd, d ^ (4 * n - 2) : ℕ) : ℚ) := by
  sorry

end OMA.S_oeis_a207262
