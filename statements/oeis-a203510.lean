import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OMA.S_oeis_a203510

/-- `A203482 n = ∏_{1 ≤ j < k ≤ n} (k! + j!)`. -/
def A203482 (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 n, ∏ j ∈ Finset.Ico 1 k, (Nat.factorial k + Nat.factorial j)

/-- The superfactorial `A000178 m = ∏_{i = 1}^m i!` (with `A000178 0 = 1`).
Note that the `n`-th term of `A000178` (indexed from 1, i.e., `BarnesG(n+1) = ∏_{i=1}^n (i-1)!`)
equals `superfactorial (n - 1)`. -/
def superfactorial (m : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 m, Nat.factorial i

/-- Conjecture (OEIS A203510): for every `n ≥ 1`, `A203482(n) / A000178(n-1)` is an integer,
i.e., `∏_{i=1}^{n-1} i!` divides `∏_{1 ≤ j < k ≤ n} (k! + j!)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → superfactorial (n - 1) ∣ A203482 n := by
  sorry

end OMA.S_oeis_a203510
