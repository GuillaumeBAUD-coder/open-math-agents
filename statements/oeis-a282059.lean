import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace OMA.S_oeis_a282059

/-- Number of primes in `[10*k, 10*k + 30]`. -/
def countPrimes (k : ℕ) : ℕ :=
  ((Finset.Icc (10 * k) (10 * k + 30)).filter Nat.Prime).card

/-- OEIS A282059: for every `k ≥ 1`, there are at most `8` primes between `10*k` and
`10*k + 30`, and whenever there are `8` primes, `k ≡ 1 (mod 21)` or `k ≡ 17 (mod 21)`. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → countPrimes k ≤ 8) ∧
    (∀ k : ℕ, 1 ≤ k → countPrimes k = 8 → k % 21 = 1 ∨ k % 21 = 17) := by
  sorry

end OMA.S_oeis_a282059
