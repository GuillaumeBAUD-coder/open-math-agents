import Mathlib

/-!
# Squarefreeness of leftover Fibonacci factors

For each positive index, divide its Fibonacci number by the least common
multiple of the Fibonacci numbers at its proper divisors. The empty least
common multiple is `1`. The question asks whether the resulting factor is
squarefree at every positive index other than `6`, where it is `4`.

Original question
https://mathoverflow.net/questions/273933

Formalization by @llostinthesauce.
-/

namespace OMA.S_mo_273933

/-- The Fibonacci number at `n` divided by the LCM for its proper divisors. -/
def leftover (n : ℕ) : ℕ := Nat.fib n / (n.properDivisors.lcm Nat.fib)

theorem main : ∀ n : ℕ, 0 < n → n ≠ 6 → Squarefree (leftover n) := by
  sorry

end OMA.S_mo_273933
