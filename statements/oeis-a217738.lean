import Mathlib

/-!
# A217738: Numbers k such that Fibonacci(k) is divisible by k*(k+1).

Source: https://oeis.org/A217738
Credit: @azmiozgen

Conjectures (from the entry): the sequence is infinite; all terms are divisible by 12.

Formalization notes:
* The terms are the k ≥ 1 with k(k+1) dividing `Nat.fib k`.
* Controls (computed): the terms below 2200 are 60, 108, 180, 240, 540, 600, 660, 768, 1008, 1200,
  1320, 1620, 1800, 1860, 2160, as in the entry.
-/

namespace OMA.S_oeis_a217738

/-- Both conjectures of the entry. -/
theorem main :
    {k : ℕ | 0 < k ∧ k * (k + 1) ∣ Nat.fib k}.Infinite ∧
      ∀ k : ℕ, 0 < k → k * (k + 1) ∣ Nat.fib k → 12 ∣ k := by
  sorry

end OMA.S_oeis_a217738
