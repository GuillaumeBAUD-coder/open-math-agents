import Mathlib

/-!
# A236020: Natural numbers n sorted by increasing values of k(n) = log_tau(n) (sigma(n))

Source: https://oeis.org/A236020
Credit: @xor2k

Formalizes the OEIS A236020 conjecture:
Conjecture: every natural number n has a unique value of k(n).
(The entry itself notes that the conjecture is wrong: k(5) = k(22) = log(6)/log(2), Amiram Eldar,
Jan 17 2021.)

Conventions:
* `k n = log_tau(n) (sigma(n)) = log(sigma(n)) / log(tau(n))`, written with `Real.logb`, where
  `tau(n)` (A000005) is `n.divisors.card` and `sigma(n)` (A000203) is `ArithmeticFunction.sigma 1 n`.
* Natural numbers are the positive integers. For `n = 1` we have `tau(1) = 1`, so `log_1` is
  undefined mathematically; Lean gives `k 1 = 0`. This value is never needed below.
* Unique value of `k(n)` is read as: `k` is injective on the positive integers.
-/

namespace OMA.S_oeis_a236020

/-- `k(n) = log_tau(n) (sigma(n))`, with `tau(n)` the number and `sigma(n)` the sum of divisors. -/
noncomputable def k (n : ℕ) : ℝ :=
  Real.logb (n.divisors.card : ℝ) (ArithmeticFunction.sigma 1 n : ℝ)

/-- Distinct positive integers have distinct values of `k`. -/
theorem main : ∀ m n : ℕ, 0 < m → 0 < n → k m = k n → m = n := by
  sorry

end OMA.S_oeis_a236020
