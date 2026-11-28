import Mathlib

namespace OMA.S_oeis_a111159

/-- The Fibonacci divisor sum A111075. -/
def a111075 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, Nat.fib n / Nat.fib d

/-- The OEIS A111159 conjecture, with a divisor-count criterion for membership. -/
theorem main :
    (∀ n : ℕ, 0 < n →
      (Odd (a111075 n) ↔
        if 3 ∣ n then Odd (((n / 3).divisors.filter Odd).card)
        else Odd n.divisors.card)) ∧
    (∀ m : ℕ, 0 < m → ¬ 3 ∣ m → Odd (a111075 (m ^ 2))) ∧
    (∀ m : ℕ, 0 < m → Odd (a111075 (3 * m ^ 2)) ∧
      Odd (a111075 (6 * m ^ 2))) := by
  sorry

end OMA.S_oeis_a111159
