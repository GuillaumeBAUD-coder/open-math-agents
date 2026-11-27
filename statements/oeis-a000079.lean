import Mathlib

/-!
# OEIS A000079

Source: https://oeis.org/A000079 (Powers of 2: a(n) = 2^n; OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

The comment on A000079 states: the Collatz conjecture (the hailstone sequence will eventually
reach the number 1, regardless of which positive integer is chosen initially) may be restated
as: the hailstone sequence will eventually reach a power of 2, regardless of which positive
integer is chosen initially.

We state this restated form. Conventions (standard, as in OEIS A006370 and A070165):
- The Collatz (hailstone) map sends an even `n` to `n / 2` and an odd `n` to `3 * n + 1`.
- The hailstone sequence started at `n` is `n, T n, T (T n), ...`, i.e. `T^[k] n` for `k ≥ 0`
  (the starting value itself counts, so a starting power of 2 trivially qualifies).
- A power of 2 is a number `2 ^ j` with `j : ℕ` (so `1 = 2 ^ 0` is a power of 2).
-/

namespace OMA.S_oeis_a000079

/-- The Collatz (hailstone) map: `n / 2` for even `n`, `3 * n + 1` for odd `n`. -/
def collatz (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

theorem main : ∀ n : ℕ, 0 < n → ∃ k j : ℕ, collatz^[k] n = 2 ^ j := by
  sorry

end OMA.S_oeis_a000079
