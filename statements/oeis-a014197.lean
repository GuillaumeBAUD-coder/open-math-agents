import Mathlib

/-!
# A014197: Number of numbers m with Euler phi(m) = n.

Source: https://oeis.org/A014197
Credit: @divmxnd0x

Conjecture (Carmichael's totient conjecture, stated in A014197): there are no 1's in this
sequence.

Formalization notes:
* `a n` counts the positive integers `m` with `phi(m) = n` (offset 1: `a 1, a 2, ... = 2, 3, 0, 4,
  0, 4, 0, 5, ...`). For `n ≥ 1` this set is finite (`phi(m) ≥ sqrt(m / 2)`), so `Nat.card` is its
  number of elements.
* "No 1's in the sequence" is stated for every index `n ≥ 1`.
-/

namespace OMA.S_oeis_a014197

/-- A014197(n): the number of positive `m` with `phi(m) = n`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {m : ℕ // 0 < m ∧ Nat.totient m = n}

/-- Carmichael's conjecture: `a(n) ≠ 1` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≠ 1 := by
  sorry

end OMA.S_oeis_a014197
