import Mathlib

/-!
# A006577: Number of halving and tripling steps to reach 1 in '3x+1' problem, or -1 if 1 is never reached.

Source: https://oeis.org/A006577
Credit: @divmxnd0x

Conjecture (the 3x+1 or Collatz problem, stated in A006577): starting from any `n`, repeatedly
halving even numbers and sending odd `m` to `3m + 1` always reaches `1`; equivalently, the
sequence never takes the value `-1`.

Formalization notes:
* `collatz` is one step of the map (`m ↦ m / 2` for even `m`, `m ↦ 3m + 1` for odd `m`).
* `a n` is the number of steps needed to reach `1` from `n` (the least `k` with
  `collatz^[k] n = 1`), or `-1` if `1` is never reached, exactly as in the name of A006577; the
  offset is `1` (so `a 1 = 0`, `a 2 = 1`, `a 3 = 7`, `a 4 = 2`, ...).
* The conjecture is stated over the indices of the sequence, `n ≥ 1`: `a n ≠ -1`.
-/

namespace OMA.S_oeis_a006577

/-- One step of the `3x+1` map. -/
def collatz (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

open Classical in
/-- A006577(n): the number of `3x+1` steps from `n` to `1`, or `-1` if `1` is never reached. -/
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ k : ℕ, collatz^[k] n = 1 then (Nat.find h : ℤ) else -1

/-- The Collatz conjecture: for every `n ≥ 1`, `a(n) ≠ -1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≠ -1 := by
  sorry

end OMA.S_oeis_a006577
