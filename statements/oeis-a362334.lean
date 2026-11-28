import Mathlib

/-!
# A362334: sums of Euler's totient at arguments two apart

Source: https://oeis.org/A362334 (Alexandre Herrera, April 2023).
Credit: @asher-lanzone

The sequence starts at index 1, so both neighbors of `2 * n` occur for every positive `n`.
-/

namespace OMA.S_oeis_a362334

def a (n : ℕ) : ℕ := n.totient + (n + 2).totient

theorem main : ∀ n : ℕ, 1 ≤ n →
    a (2 * n) ≤ a (2 * n - 1) ∧ a (2 * n) < a (2 * n + 1) := by
  sorry

end OMA.S_oeis_a362334
